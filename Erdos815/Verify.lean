/-
# 公理验收

本任务的验收口径:`#print axioms` 只允许出现
`propext`、`Classical.choice`、`Quot.sound`。
出现表示「未证」的公理,或表示「用了编译期求值 tactic」的求值公理,即不合格。
(这两个公理的确切名字写在验收脚本里,此处刻意不写,以免触发机械门的字面量扫描。)

用 `lake env lean Erdos815/Verify.lean` 运行(它不进 Erdos815.lean 的 import 图)。
-/
import Erdos815

namespace Erdos815

-- ===== T2.5(step 1 已闭合)=====
#print axioms theorem_2_5
#print axioms aSeq_isKAvoiding
#print axioms aSeq_isOddEven
#print axioms aSeq_matches_paper

-- ===== P-crit(step 2 已闭合)=====
#print axioms gt_isDegree3Critical
#print axioms GT_card_edgeFinset
#print axioms Is13Tree.two_mul_card_leafFinset
#print axioms GT_degree_inl
#print axioms GT_degree_inr

-- ===== L2.1(i)(step 3 已闭合)=====
#print axioms no_cycle_23_of_no_leaf_path_20
#print axioms lemma_2_1_i_mp
#print axioms leafPath_of_cycle_cons
#print axioms cycle_cons_xy
#print axioms edge_xy_mem_edges_of_odd
#print axioms exists_walk_of_support_inl
#print axioms leaf_color_eq

-- ===== L2.2(step 4)=====
-- 交付给 step 5 的两个接口 + 1-3 树:
#print axioms lemma_2_2_iv_only_if
#print axioms TTree_isEvenTree
#print axioms TTree_is13Tree
-- 支撑它们的中间结论:
#print axioms lemma_2_2_i
#print axioms leafLeafPath_length
#print axioms leafLeafPath_le_of_idx_eq
#print axioms leafLeafPath_eq_of_idx_ne
#print axioms TTree_isTree
#print axioms TTree_isAcyclic
#print axioms TTree_preconnected
#print axioms isLeaf_iff
#print axioms pathV_isDeg3
#print axioms treeV_isDeg3
#print axioms treeV_isLeaf
#print axioms exists_upPath
#print axioms exists_segPath
#print axioms exists_leafWalk_of_idx_eq
#print axioms exists_leafPath_of_idx_ne
-- 论文里存在、本链路不使用的三条(step 5 回头闭合):
#print axioms lemma_2_2_ii
#print axioms lemma_2_2_iii
#print axioms lemma_2_2_iv

-- ===== T1.3(ii) 与 T1.2(step 5)=====
-- 🔴 **最终验收看的就是下面第一行**:`erdos_815` 的公理足迹必须只有
-- `propext` / `Classical.choice` / `Quot.sound`。
#print axioms erdos_815
#print axioms theorem_1_2
#print axioms theorem_1_3_ii
-- 支撑它们的中间结论:
#print axioms aSeq_le_nine
#print axioms xA_isOddEven
#print axioms xA_xMax_lt
#print axioms famG_isDegree3Critical
#print axioms famG_no_cycle
#print axioms famG_unbounded
#print axioms card_TVtx_ge
#print axioms IsDegree3Critical.of_iso
#print axioms hasCycleOfLength_of_iso
#print axioms finGraph_isDegree3Critical
#print axioms finGraph_no_cycle

end Erdos815
