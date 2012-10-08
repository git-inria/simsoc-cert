(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Extraction of the Arm6 simulator.
*)

Require Extraction Arm6_Simul.

Extraction NoInline Arm6_Functions.Semantics.if_CurrentModeHasSPSR.

Cd "extraction".

Extraction Library Arm6.
Extraction Library Arm6_Config.
Extraction Library Arm6_Proc.
Extraction Library Arm6_SCC.
Extraction Library Arm6_State.
Extraction Library Arm6_Exception.
Extraction Library Arm6_Functions.
Extraction Library Arm6_Message.
Extraction Library Arm6_Simul.

Extraction Library Arm6_Dec.
Extraction Library Arm6_Inst.
