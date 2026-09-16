import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup000
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup001
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup002
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup003
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup004
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup005
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup006
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup007
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup008
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup009
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup010
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup011
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup012
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup013
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup014
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup015
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup016
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup017
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup018
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup019
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup020
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup021
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup022
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup023
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup024
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup025
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup026
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup027
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup028
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup029
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup030
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup031
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup032
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup033
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup034
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup035
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup036
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup037
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup038
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup039
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup040
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup041
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup042
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup043
import LiuWang.Proof.Campaign20260915.RSMediumRange.ChainGroup044

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem fullMediumCertificate :
    CertifiedChunk Chunk0000Start Chunk0705End := by
  exact ((((((((((((((((((((((((((((((((((((((((((((ChainGroup000Certified.trans ChainGroup001Certified).trans ChainGroup002Certified).trans ChainGroup003Certified).trans ChainGroup004Certified).trans ChainGroup005Certified).trans ChainGroup006Certified).trans ChainGroup007Certified).trans ChainGroup008Certified).trans ChainGroup009Certified).trans ChainGroup010Certified).trans ChainGroup011Certified).trans ChainGroup012Certified).trans ChainGroup013Certified).trans ChainGroup014Certified).trans ChainGroup015Certified).trans ChainGroup016Certified).trans ChainGroup017Certified).trans ChainGroup018Certified).trans ChainGroup019Certified).trans ChainGroup020Certified).trans ChainGroup021Certified).trans ChainGroup022Certified).trans ChainGroup023Certified).trans ChainGroup024Certified).trans ChainGroup025Certified).trans ChainGroup026Certified).trans ChainGroup027Certified).trans ChainGroup028Certified).trans ChainGroup029Certified).trans ChainGroup030Certified).trans ChainGroup031Certified).trans ChainGroup032Certified).trans ChainGroup033Certified).trans ChainGroup034Certified).trans ChainGroup035Certified).trans ChainGroup036Certified).trans ChainGroup037Certified).trans ChainGroup038Certified).trans ChainGroup039Certified).trans ChainGroup040Certified).trans ChainGroup041Certified).trans ChainGroup042Certified).trans ChainGroup043Certified).trans ChainGroup044Certified)

theorem fullMediumBounds_of_start (hs : Chunk0000Start.Actual) :
    ∀ x : ℝ, 16000 ≤ x → x ≤ 100000000 → MediumBounds x := by
  have h := fullMediumCertificate.2 hs
  have ht := certified_terminal (s := Chunk0705End)
    (b := 100000000) (root := 10000000000) (code := 2923070177584700571302653240642858333912818974722)
    (by norm_num [Chunk0705End]) (by norm_num [Chunk0705End])
    (by decide +kernel) (by decide +kernel) h.1
  intro x hx hhi
  by_cases hlast : x < Chunk0705End.p
  · exact h.2 x hx hlast
  · exact ht x (le_of_not_gt hlast) hhi

#print axioms fullMediumCertificate
#print axioms fullMediumBounds_of_start
end LiuWang.Proof.Campaign20260915.RSMediumRange
