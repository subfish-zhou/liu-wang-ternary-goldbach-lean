import LiuWang.Proof.ChebyshevBound.IntegratedFormula.Sharp

/-! # 原阈值尖锐 psi 总量界的完整类型、实际对象及递归公理检查入口。 -/

set_option pp.universes true
set_option pp.fullNames true
set_option pp.notation false

open LiuWang.Proof.ChebyshevBound.HighHeight
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

#check hasMellin_zeroSum
#check hasMellin_mangoldtSum
#check hasMellin_gammaSum
#check hasMellin_spectralMellin
#check verticalIntegrable_smoothed_logderiv
#check integratedPsi_eq_spectral
#check integratedPsi_difference_formula
#check integratedPsi_difference_upper
#check psi_le_sharp_real
#check psi_le_sharp
#check sum_mangoldt_Icc_le_sharp
#check sum_mangoldt_Ioc_le_sharp
#check sum_mangoldt_sq_le_sharp

#print Chebyshev.psi
#print ArithmeticFunction.vonMangoldt
#print integratedPsi
#print integratedZeroTerm
#print powerCut
#print triangle
#print zeroMellinTerm
#print mangoldtTriangle
#print gammaMellinTerm
#print poleMellin
#print spectralMellin
#print gammaCorrection

#print axioms integratedPsi_eq_spectral
#print axioms integratedPsi_difference_formula
#print axioms psi_le_sharp_real
#print axioms psi_le_sharp
#print axioms sum_mangoldt_Icc_le_sharp
#print axioms sum_mangoldt_Ioc_le_sharp
#print axioms sum_mangoldt_sq_le_sharp
