import NormalForms

/-!
Lightweight axiom-audit smoke script for the current public API surface.

Replace this with a declaration-discovering audit once the smoke-script phase is
over.
-/

#print axioms NormalForms.Matrix.Hermite.HNFResult.toCertificate
#print axioms NormalForms.Matrix.Hermite.hermiteNormalForm
#print axioms NormalForms.Matrix.Smith.SNFResult.toCertificate
#print axioms NormalForms.Matrix.Smith.smithNormalForm
#print axioms NormalForms.Bridge.MathlibPID.pidSmithColumnSpan_eq_range_mulVecLin
#print axioms NormalForms.Examples.AbelianGroups.presentationColumnSpanBridgeSmoke
