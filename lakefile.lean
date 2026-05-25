import Lake
open Lake DSL

package "Microvmm" where
  version := v!"0.0.1"
  moreLinkObjs := #[`@/microvmm_shim, `@/microvmm_virtio_rng_probe_guest]

lean_lib "Microvmm"

lean_lib "MicrovmmProof"

@[default_target]
lean_exe "microvmm" where
  root := `Main

lean_exe "microvmm-test" where
  root := `MicrovmmTest

target microvmm_shim (pkg : NPackage __name__) : System.FilePath := do
  let srcJob <- inputTextFile <| pkg.dir / "ffi" / "shim.c"
  let oFile := pkg.buildDir / "ffi" / "microvmm_shim.o"
  let leanIncludeDir <- getLeanIncludeDir
  buildO oFile srcJob #[("-I"), leanIncludeDir.toString]

target microvmm_virtio_rng_probe_guest (pkg : NPackage __name__) : System.FilePath := do
  let srcJob <- inputTextFile <| pkg.dir / "ffi" / "virtio_rng_probe_guest.S"
  let oFile := pkg.buildDir / "ffi" / "virtio_rng_probe_guest.o"
  buildO oFile srcJob #[]

 require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"
