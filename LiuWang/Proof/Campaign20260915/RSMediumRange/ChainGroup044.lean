import LiuWang.Proof.Campaign20260915.RSMediumRange.Chunk0704
import LiuWang.Proof.Campaign20260915.RSMediumRange.Chunk0705

set_option autoImplicit false
set_option Elab.async false
namespace LiuWang.Proof.Campaign20260915.RSMediumRange
theorem ChainGroup044Certified : CertifiedChunk Chunk0704Start Chunk0705End := by
  exact (Chunk0704Certified.trans Chunk0705Certified)
end LiuWang.Proof.Campaign20260915.RSMediumRange
