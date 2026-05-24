#define _GNU_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <sched.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <sys/types.h>
#include <unistd.h>

static const char ready_marker[] = "MICROVMM_INITRD_READY\n";
static const char prompt[] = "microvmm> ";
static const char help_text[] =
    "commands: help, echo TEXT, cmdline, mounts, reboot, poweroff\n";

static int write_all(int fd, const char *buffer, size_t length) {
  size_t written = 0;

  while (written < length) {
    ssize_t count = write(fd, buffer + written, length - written);
    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    written += (size_t)count;
  }

  return 0;
}

static int write_string(int fd, const char *text) {
  return write_all(fd, text, strlen(text));
}

static void write_errno_message(int fd, const char *action, int errnum) {
  char buffer[160];
  int length = snprintf(buffer, sizeof(buffer), "%s failed (errno=%d)\n", action,
                        errnum);

  if (length <= 0) {
    return;
  }
  if ((size_t)length >= sizeof(buffer)) {
    length = (int)(sizeof(buffer) - 1);
  }
  (void)write_all(fd, buffer, (size_t)length);
}

static int ensure_dir(const char *path, mode_t mode) {
  struct stat status;

  if (stat(path, &status) == 0) {
    return S_ISDIR(status.st_mode) ? 0 : -1;
  }
  if (mkdir(path, mode) == 0 || errno == EEXIST) {
    return 0;
  }
  return -1;
}

static int ensure_char_device(const char *path, mode_t mode, unsigned int major_id,
                              unsigned int minor_id) {
  struct stat status;

  if (stat(path, &status) == 0) {
    return S_ISCHR(status.st_mode) ? 0 : -1;
  }
  if (mknod(path, mode | S_IFCHR, makedev(major_id, minor_id)) == 0 ||
      errno == EEXIST) {
    return 0;
  }
  return -1;
}

static void mount_if_needed(int console_fd, const char *source, const char *target,
                            const char *fstype, unsigned long flags,
                            const char *data) {
  if (mount(source, target, fstype, flags, data) == 0 || errno == EBUSY) {
    return;
  }

  if (console_fd >= 0) {
    char action[64];
    int length = snprintf(action, sizeof(action), "mount %s", target);
    if (length > 0) {
      write_errno_message(console_fd, action, errno);
    }
  }
}

static void setup_dev_nodes(void) {
  (void)ensure_dir("/dev", 0755);

  if (mount("devtmpfs", "/dev", "devtmpfs", 0, "mode=0755") < 0 &&
      errno != EBUSY) {
    /* Fall back to a tiny static /dev when devtmpfs is unavailable. */
  }

  (void)ensure_char_device("/dev/console", 0600, 5, 1);
  (void)ensure_char_device("/dev/null", 0666, 1, 3);
  (void)ensure_char_device("/dev/tty", 0666, 5, 0);
  (void)ensure_char_device("/dev/ttyS0", 0600, 4, 64);
}

static int redirect_console(void) {
  int console_fd = open("/dev/console", O_RDWR | O_CLOEXEC);

  if (console_fd < 0) {
    console_fd = open("/dev/ttyS0", O_RDWR | O_CLOEXEC);
  }
  if (console_fd < 0) {
    return -1;
  }

  (void)setsid();
  (void)ioctl(console_fd, TIOCSCTTY, 0);

  if (dup2(console_fd, STDIN_FILENO) < 0 || dup2(console_fd, STDOUT_FILENO) < 0 ||
      dup2(console_fd, STDERR_FILENO) < 0) {
    close(console_fd);
    return -1;
  }

  if (console_fd > STDERR_FILENO) {
    close(console_fd);
  }

  return STDOUT_FILENO;
}

static void stream_file(int console_fd, const char *path) {
  char buffer[256];
  bool saw_newline = false;
  int file_fd = open(path, O_RDONLY | O_CLOEXEC);

  if (file_fd < 0) {
    write_errno_message(console_fd, path, errno);
    return;
  }

  for (;;) {
    ssize_t count = read(file_fd, buffer, sizeof(buffer));
    if (count == 0) {
      break;
    }
    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      write_errno_message(console_fd, path, errno);
      close(file_fd);
      return;
    }
    if (buffer[count - 1] == '\n') {
      saw_newline = true;
    }
    if (write_all(console_fd, buffer, (size_t)count) < 0) {
      close(file_fd);
      return;
    }
  }

  close(file_fd);
  if (!saw_newline) {
    (void)write_string(console_fd, "\n");
  }
}

static char *trim_left(char *line) {
  while (*line == ' ' || *line == '\t') {
    ++line;
  }
  return line;
}

static void trim_right(char *line) {
  size_t length = strlen(line);

  while (length > 0 && (line[length - 1] == ' ' || line[length - 1] == '\t')) {
    line[length - 1] = '\0';
    --length;
  }
}

static ssize_t read_line(int fd, char *buffer, size_t capacity) {
  size_t length = 0;

  if (capacity == 0) {
    return -1;
  }

  for (;;) {
    char byte;
    ssize_t count = read(fd, &byte, sizeof(byte));

    if (count == 0) {
      return -1;
    }
    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      return -1;
    }
    if (byte == '\r') {
      continue;
    }
    if (byte == '\n') {
      break;
    }
    if (length + 1 < capacity) {
      buffer[length++] = byte;
    }
  }

  buffer[length] = '\0';
  return (ssize_t)length;
}

static void run_reboot(int console_fd, int command, const char *name) {
  sync();
  if (reboot(command) < 0) {
    write_errno_message(console_fd, name, errno);
  }
}

static void handle_command(int console_fd, char *line) {
  char *command = trim_left(line);

  trim_right(command);
  if (*command == '\0') {
    return;
  }

  if (strcmp(command, "help") == 0) {
    (void)write_string(console_fd, help_text);
    return;
  }

  if (strncmp(command, "echo ", 5) == 0) {
    (void)write_string(console_fd, command + 5);
    (void)write_string(console_fd, "\n");
    return;
  }

  if (strcmp(command, "cmdline") == 0) {
    stream_file(console_fd, "/proc/cmdline");
    return;
  }

  if (strcmp(command, "mounts") == 0) {
    stream_file(console_fd, "/proc/mounts");
    return;
  }

  if (strcmp(command, "reboot") == 0) {
    run_reboot(console_fd, RB_AUTOBOOT, "reboot");
    return;
  }

  if (strcmp(command, "poweroff") == 0) {
    run_reboot(console_fd, RB_POWER_OFF, "poweroff");
    return;
  }

  (void)write_string(console_fd, "unknown command\n");
}

int main(void) {
  char line[256];
  int console_fd;

  umask(022);
  if (chdir("/") < 0) {
    return 1;
  }
  (void)ensure_dir("/proc", 0555);
  (void)ensure_dir("/sys", 0555);
  (void)ensure_dir("/tmp", 01777);
  (void)ensure_dir("/run", 0755);
  (void)ensure_dir("/etc", 0755);
  setup_dev_nodes();

  console_fd = redirect_console();
  if (console_fd < 0) {
    console_fd = STDOUT_FILENO;
  }

  mount_if_needed(console_fd, "proc", "/proc", "proc", 0, "");
  mount_if_needed(console_fd, "sysfs", "/sys", "sysfs", 0, "");
  setup_dev_nodes();

  (void)write_string(console_fd, ready_marker);
  (void)write_string(console_fd, help_text);

  for (;;) {
    (void)write_string(console_fd, prompt);
    if (read_line(STDIN_FILENO, line, sizeof(line)) < 0) {
      (void)write_string(console_fd, "console input closed\n");
      pause();
      continue;
    }
    handle_command(console_fd, line);
  }
}