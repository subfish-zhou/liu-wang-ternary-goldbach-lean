import LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.ElementaryBounds

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate

def endpoint : PureKind → Bool → ℝ
  | .linear, false => 9.404415130615234375
  | .linear, true => 9.4044153690338134765625
  | .quadratic, false => 10.935331821441650390625
  | .quadratic, true => 10.9353320598602294921875
  | .cubic, false => 12.5753672122955322265625
  | .cubic, true => 12.575367450714111328125

def endpointLogLo : PureKind → Bool → ℝ
  | .linear, false => 2.2411792727
  | .linear, true => 2.241179298
  | .quadratic, false => 2.3919989975
  | .quadratic, true => 2.3919990193
  | .cubic, false => 2.5317399162
  | .cubic, true => 2.5317399352

def endpointLogHi : PureKind → Bool → ℝ
  | .linear, false => 2.2411792748
  | .linear, true => 2.2411793001
  | .quadratic, false => 2.3919989996
  | .quadratic, true => 2.3919990214
  | .cubic, false => 2.5317399183
  | .cubic, true => 2.5317399373

def endpointExpLo : PureKind → Bool → ℝ
  | .linear, false => 0.55556151072006
  | .linear, true => 0.55556150244155
  | .quadratic, false => 0.50486801573804
  | .quadratic, true => 0.50486800821492
  | .cubic, false => 0.45568183157759
  | .cubic, true => 0.4556818247874

def endpointExpHi : PureKind → Bool → ℝ
  | .linear, false => 0.55556151072007
  | .linear, true => 0.55556150244156
  | .quadratic, false => 0.50486801573805
  | .quadratic, true => 0.50486800821493
  | .cubic, false => 0.4556818315776
  | .cubic, true => 0.45568182478741

def finalArgument : PureKind → ℝ
  | .linear => -2.0299029536
  | .quadratic => -1.3965953451
  | .cubic => -0.6976783906

def finalExpHi : PureKind → ℝ
  | .linear => 0.60201330150149
  | .quadratic => 0.70528814999667
  | .cubic => 0.83994438501679

def certifiedValue : PureKind → ℝ
  | .linear => 0.000002563555388
  | .quadratic => 0.000124221398835
  | .cubic => 0.02798295146629

def valueMargin : PureKind → ℝ
  | .linear => 0.000000000044612
  | .quadratic => 0.000005778601165
  | .cubic => 0.00001704853371

theorem certifiedValue_budget (j : PureKind) :
    certifiedValue j + valueMargin j = sourceScalarBudget j ∧ 0 < valueMargin j := by
  cases j <;> norm_num [certifiedValue, valueMargin, sourceScalarBudget]

theorem endpoint_domain (j : PureKind) :
    8 < endpoint j false ∧ endpoint j false < endpoint j true ∧ endpoint j true < 16 := by
  cases j <;> norm_num [endpoint]

end LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate
