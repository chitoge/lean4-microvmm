import Microvmm.Common
import Microvmm.Linux
import Microvmm.VirtioMmio

namespace Microvmm

open Kvm

def probeApiVersion : IO (Result UInt32) := do
  withKvm getApiVersion

def probeVcpuRunArea : IO (Result ProbeSuccess) := do
  withVmContext fun vmContext =>
    withVcpuContext vmContext defaultVcpuId fun vcpuContext =>
      mapIOResult (probeRunArea vcpuContext.vcpu vmContext.runAreaSize) fun _ =>
        ⟨vmContext.apiVersion, vmContext.runAreaSize, ""⟩

end Microvmm