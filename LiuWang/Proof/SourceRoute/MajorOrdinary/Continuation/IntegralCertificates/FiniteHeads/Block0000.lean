import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.BlockSoundness

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads

def data0000 : Block :=
  (.branch
  (.branch
    (.branch
      (.branch
        (.branch
          (.leaf ⟨1, 1, 1, .one, 1000000000000, 1000000000000, 1000000000000⟩)
          (.leaf ⟨2, 1, (-1), (.step 2 1 .one), 1122462048310, 1122462048310, 2244924096620⟩))
        (.branch
          (.leaf ⟨3, 2, (-1), (.step 3 1 .one), 1200936955177, 300234238795, 900702716383⟩)
          (.leaf ⟨4, 2, 0, (.step 2 2 .one), 0, 0, 0⟩)))
      (.branch
        (.branch
          (.leaf ⟨5, 4, (-1), (.step 5 1 .one), 1307660486012, 81728780376, 408643901879⟩)
          (.leaf ⟨6, 2, 1, (.step 2 1 (.step 3 1 .one)), 1348006154598, 337001538650, 2022009231897⟩))
        (.branch
          (.leaf ⟨7, 6, (-1), (.step 7 1 .one), 1383087554269, 38419098730, 268933691108⟩)
          (.leaf ⟨8, 4, 0, (.step 2 3 .one), 0, 0, 0⟩))))
    (.branch
      (.branch
        (.branch
          (.leaf ⟨9, 6, 0, (.step 3 2 .one), 0, 0, 0⟩)
          (.leaf ⟨10, 4, 1, (.step 2 1 (.step 5 1 .one)), 1467799267623, 91737454227, 917374542265⟩))
        (.branch
          (.leaf ⟨11, 10, (-1), (.step 11 1 .one), 1491301475414, 14913014755, 164043162296⟩)
          (.leaf ⟨12, 4, 0, (.step 2 2 (.step 3 1 .one)), 0, 0, 0⟩)))
      (.branch
        (.branch
          (.leaf ⟨13, 12, (-1), (.step 13 1 .one), 1533406237017, 10648654424, 138432507509⟩)
          (.leaf ⟨14, 6, 1, (.step 2 1 (.step 7 1 .one)), 1552463289156, 43123980255, 603735723561⟩))
        (.branch
          (.leaf ⟨15, 8, 1, (.step 3 1 (.step 5 1 .one)), 1570417802476, 24537778164, 368066672456⟩)
          (.leaf ⟨16, 8, 0, (.step 2 4 .one), 0, 0, 0⟩)))))
  (.branch
    (.branch
      (.branch
        (.branch
          (.leaf ⟨17, 16, (-1), (.step 17 1 .one), 1603521621513, 6263756335, 106483857679⟩)
          (.leaf ⟨18, 6, 0, (.step 2 1 (.step 3 2 .one)), 0, 0, 0⟩))
        (.branch
          (.leaf ⟨19, 18, (-1), (.step 19 1 .one), 1633524303071, 5041741677, 95793091847⟩)
          (.leaf ⟨20, 8, 0, (.step 2 2 (.step 5 1 .one)), 0, 0, 0⟩)))
      (.branch
        (.branch
          (.leaf ⟨21, 12, 1, (.step 3 1 (.step 7 1 .one)), 1661000956166, 11534728863, 242229306108⟩)
          (.leaf ⟨22, 10, 1, (.step 2 1 (.step 11 1 .one)), 1673929308739, 16739293088, 368264447923⟩))
        (.branch
          (.leaf ⟨23, 22, (-1), (.step 23 1 .one), 1686376879542, 3484249752, 80137744276⟩)
          (.leaf ⟨24, 8, 0, (.step 2 3 (.step 3 1 .one)), 0, 0, 0⟩))))
    (.branch
      (.branch
        (.branch
          (.leaf ⟨25, 20, 0, (.step 5 2 .one), 0, 0, 0⟩)
          (.leaf ⟨26, 12, 1, (.step 2 1 (.step 13 1 .one)), 1721190305692, 11952710457, 310770471862⟩))
        (.branch
          (.leaf ⟨27, 18, 0, (.step 3 3 .one), 0, 0, 0⟩)
          (.leaf ⟨28, 12, 0, (.step 2 2 (.step 7 1 .one)), 0, 0, 0⟩)))
      (.branch
        (.branch
          (.leaf ⟨29, 28, (-1), (.step 29 1 .one), 1752802563236, 2235717556, 64835809100⟩)
          (.leaf ⟨30, 8, (-1), (.step 2 1 (.step 3 1 (.step 5 1 .one))), 1762734383268, 27542724739, 826281742157⟩))
        (.branch
          (.leaf ⟨31, 30, (-1), (.step 31 1 .one), 1772394045463, 1969326718, 61049128233⟩)
          (.leaf ⟨32, 16, 0, (.step 2 5 .one), 0, 0, 0⟩))))))

theorem bound0000 : HeadBound 1 33 3151570835871 11192711845159 :=
  Block.verifies_sound (b := data0000) (by decide +kernel)

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads
