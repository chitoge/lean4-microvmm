namespace Microvmm

structure GuestPhysAddr where
  value : UInt64
deriving Repr, DecidableEq, BEq, Inhabited

structure MmioPhysAddr where
  value : UInt64
deriving Repr, DecidableEq, BEq, Inhabited

structure IoPort where
  value : UInt32
deriving Repr, DecidableEq, BEq, Inhabited

instance : Coe GuestPhysAddr UInt64 := ⟨GuestPhysAddr.value⟩

instance : Coe MmioPhysAddr UInt64 := ⟨MmioPhysAddr.value⟩

instance : Coe IoPort UInt32 := ⟨IoPort.value⟩

instance : HAdd GuestPhysAddr UInt64 GuestPhysAddr :=
  ⟨fun base offset => ⟨base.value + offset⟩⟩

inductive AccessDirection where
  | read
  | write
deriving Repr, DecidableEq

inductive IoDirection where
  | input
  | output
deriving Repr, DecidableEq

structure MmioAccess where
  address : MmioPhysAddr
  width : UInt32
  direction : AccessDirection
  value : UInt32 := 0
deriving Repr, DecidableEq

structure IoAccess where
  port : IoPort
  width : UInt32
  count : UInt32
  direction : IoDirection
  value : UInt32 := 0
deriving Repr, DecidableEq

end Microvmm