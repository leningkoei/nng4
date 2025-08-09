import NNG4.Theorems.AddAssoc
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddLeftComm

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]
))
