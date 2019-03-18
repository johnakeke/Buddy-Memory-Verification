theory Memory_Allocation_Model
imports Main
begin

subsection \<open>def of datetype\<close>
(*------------------------------------------------------------------------------------------------*)
datatype (set: 'a) tree = leaf: Leaf (L: 'a) |
                          node: Node (LL:"'a tree") (LR:"'a tree") (RL:"'a tree") (RR:"'a tree")
                        for map: tree_map   

datatype block_state_type = FREE | ALLOC
type_synonym ID = nat
type_synonym Block = "(block_state_type \<times> ID) tree"

type_synonym poolname = "string"
record Pool = zerolevelblocks :: "Block set"
              pname :: poolname

subsection \<open>def of 'a tree function\<close>
(*------------------------------------------------------------------------------------------------*)
definition compare2 :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "compare2 a b \<equiv> (if a > b then a else b)"

definition compare4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "compare4 a b c d \<equiv> (let c1 = compare2 a b;
                                 c2 = compare2 c1 c in compare2 c2 d)"

fun get_level' :: "'a tree \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat"
  where "get_level' (Leaf x) b n = (if (x = b) then n else 0)" |
        "get_level' (Node n1 n2 n3 n4) b n = compare4 (get_level' n1 b (Suc n))
                                                      (get_level' n2 b (Suc n))
                                                      (get_level' n3 b (Suc n))
                                                      (get_level' n4 b (Suc n))"

definition get_level :: "'a tree \<Rightarrow> 'a \<Rightarrow> nat"
  where "get_level B b \<equiv> get_level' B b 0"

lemma level_notbelong:
  "b \<notin> set B \<Longrightarrow>
  get_level' B b lv = 0"
proof(induct B arbitrary: lv)
case (Leaf x)
  then show ?case by auto
next
  case (Node B1 B2 B3 B4)
  have b1: "b \<notin> set B1"
    using Node.prems by auto 
  have b2: "b \<notin> set B2"
    using Node.prems by auto 
  have b3: "b \<notin> set B3"
    using Node.prems by auto 
  have b4: "b \<notin> set B4"
    using Node.prems by auto 
  have l_node': "get_level' (Node B1 B2 B3 B4) b lv =
                compare4 (get_level' B1 b (Suc lv))
                         (get_level' B2 b (Suc lv))
                         (get_level' B3 b (Suc lv))
                         (get_level' B4 b (Suc lv))"
    using get_level'.simps(2) by auto
  have l1: "get_level' B1 b (Suc lv) = 0"
    using Node.hyps(1) b1 by auto 
  have l2: "get_level' B2 b (Suc lv) = 0"
    using Node.hyps(2) b2 by auto 
  have l3: "get_level' B3 b (Suc lv) = 0"
    using Node.hyps(3) b3 by auto 
  have l4: "get_level' B4 b (Suc lv) = 0"
    using Node.hyps(4) b4 by auto 
  have l_node: "compare4 (get_level' B1 b (Suc lv))
                         (get_level' B2 b (Suc lv))
                         (get_level' B3 b (Suc lv))
                         (get_level' B4 b (Suc lv)) = 0"
    unfolding compare4_def Let_def compare2_def l1 l2 l3 l4 by auto
  show ?case using l_node' l_node by auto
qed

fun get_level_node' :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> nat \<Rightarrow> nat"
  where "get_level_node' (Leaf x) b n = (if leaf b \<and> (L b) = x then n else 0)" |
        "get_level_node' (Node n1 n2 n3 n4) b n = (if (Node n1 n2 n3 n4) = b then n
                                                  else compare4 (get_level_node' n1 b (Suc n))
                                                                (get_level_node' n2 b (Suc n))
                                                                (get_level_node' n3 b (Suc n))
                                                                (get_level_node' n4 b (Suc n)))"

definition get_level_node :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> nat"
  where "get_level_node B b \<equiv> get_level_node' B b 0"

lemma level_node_notbelong:
  "leaf b \<Longrightarrow>
  L b \<notin> set B \<Longrightarrow>
  get_level_node' B b lv = 0"
proof(induct B arbitrary: lv)
case (Leaf x)
  then show ?case by auto
next
  case (Node B1 B2 B3 B4)
  have b1: "L b \<notin> set B1"
    using Node.prems by auto 
  have b2: "L b \<notin> set B2"
    using Node.prems by auto 
  have b3: "L b \<notin> set B3"
    using Node.prems by auto 
  have b4: "L b \<notin> set B4"
    using Node.prems by auto 
  have node_not_l: "Node B1 B2 B3 B4 \<noteq> b"
    using Node.prems(1) by auto
  have l_node': "get_level_node' (Node B1 B2 B3 B4) b lv =
                compare4 (get_level_node' B1 b (Suc lv))
                         (get_level_node' B2 b (Suc lv))
                         (get_level_node' B3 b (Suc lv))
                         (get_level_node' B4 b (Suc lv))"
    using get_level_node'.simps(2) node_not_l by auto
  have l1: "get_level_node' B1 b (Suc lv) = 0"
    using Node.hyps(1) Node.prems(1) b1 by auto 
  have l2: "get_level_node' B2 b (Suc lv) = 0"
    using Node.hyps(2) Node.prems(1) b2 by auto 
  have l3: "get_level_node' B3 b (Suc lv) = 0"
    using Node.hyps(3) Node.prems(1) b3 by auto 
  have l4: "get_level_node' B4 b (Suc lv) = 0"
    using Node.hyps(4) Node.prems(1) b4 by auto
  have l_node: "compare4 (get_level_node' B1 b (Suc lv))
                         (get_level_node' B2 b (Suc lv))
                         (get_level_node' B3 b (Suc lv))
                         (get_level_node' B4 b (Suc lv)) = 0"
    unfolding compare4_def Let_def compare2_def using l1 l2 l3 l4 by auto
  show ?case using l_node' l_node by auto
qed

lemma level_node_notbelong2:
  "node b \<Longrightarrow>
  \<not> tree.set b \<subseteq> tree.set B \<Longrightarrow>
  get_level_node' B b lv = 0"
proof(induct B arbitrary: lv)
  case (Leaf x)
  show ?case using Leaf.prems(1) by auto
next
  case (Node B1 B2 B3 B4)
  have not_eq: "b \<noteq> Node B1 B2 B3 B4"
    using Node.prems(2) by blast 
  have b1: "\<not> tree.set b \<subseteq> tree.set B1"
    using Node.prems(2) dual_order.trans by auto
  have b2: "\<not> tree.set b \<subseteq> tree.set B2"
    using Node.prems(2) dual_order.trans by auto
  have b3: "\<not> tree.set b \<subseteq> tree.set B3"
    using Node.prems(2) dual_order.trans by auto
  have b4: "\<not> tree.set b \<subseteq> tree.set B4"
    using Node.prems(2) dual_order.trans by auto
  have l1: "get_level_node' B1 b (Suc lv) = 0"
    using Node.hyps(1) Node.prems(1) b1 by auto
  have l2: "get_level_node' B2 b (Suc lv) = 0"
    using Node.hyps(2) Node.prems(1) b2 by auto
  have l3: "get_level_node' B3 b (Suc lv) = 0"
    using Node.hyps(3) Node.prems(1) b3 by auto
  have l4: "get_level_node' B4 b (Suc lv) = 0"
    using Node.hyps(4) Node.prems(1) b4 by auto
  have l_node': "get_level_node' (Node B1 B2 B3 B4) b lv =
                compare4 (get_level_node' B1 b (Suc lv))
                         (get_level_node' B2 b (Suc lv))
                         (get_level_node' B3 b (Suc lv))
                         (get_level_node' B4 b (Suc lv))"
    using get_level_node'.simps(2) not_eq by auto
  have l_node: "compare4 (get_level_node' B1 b (Suc lv))
                         (get_level_node' B2 b (Suc lv))
                         (get_level_node' B3 b (Suc lv))
                         (get_level_node' B4 b (Suc lv)) = 0"
    unfolding compare4_def Let_def compare2_def using l1 l2 l3 l4 by auto
  then show ?case using l_node' l_node by auto
qed

subsection \<open>def of function_call\<close>
(*------------------------------------------------------------------------------------------------*)
definition getnewid :: "ID set \<Rightarrow> (ID \<times> ID \<times> ID \<times> ID \<times> ID set)"
  where "getnewid ids \<equiv> let nid1 = SOME p1. p1 \<notin> ids;
                            ids1 = ids \<union> {nid1};
                            nid2 = SOME p2. p2 \<notin> ids1;
                            ids2 = ids1 \<union> {nid2};
                            nid3 = SOME p3. p3 \<notin> ids2;
                            ids3 = ids2 \<union> {nid3};
                            nid4 = SOME p4. p4 \<notin> ids3;
                            ids4 = ids3 \<union> {nid4} in
                        (nid1, nid2, nid3, nid4, ids4)"

lemma getnewid_inc: "ids \<subseteq> snd(snd(snd(snd(getnewid ids))))"
  unfolding getnewid_def Let_def by auto

lemma newid1_in_getnewid: "fst(getnewid ids) \<in> snd(snd(snd(snd(getnewid ids))))"
  unfolding getnewid_def Let_def by auto

lemma newid2_in_getnewid: "fst(snd(getnewid ids)) \<in> snd(snd(snd(snd(getnewid ids))))"
  unfolding getnewid_def Let_def by auto

lemma newid3_in_getnewid: "fst(snd(snd(getnewid ids))) \<in> snd(snd(snd(snd(getnewid ids))))"
  unfolding getnewid_def Let_def by auto

lemma newid4_in_getnewid: "fst(snd(snd(snd(getnewid ids)))) \<in> snd(snd(snd(snd(getnewid ids))))"
  unfolding getnewid_def Let_def by auto

lemma exists_p_getnewid:
  "\<exists>xa xb xc xd. getnewid ids = (xa, xb, xc, xd, ids \<union> {xa, xb, xc, xd})"
  unfolding getnewid_def Let_def by auto

lemma getnewid_diffab:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xa \<noteq> xb"
  unfolding getnewid_def Let_def
  apply auto
  by (metis (mono_tags, lifting) add.left_neutral finite_nat_set_iff_bounded lessI not_add_less2 plus_nat.simps(2) someI_ex)

lemma getnewid_diffac:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xa \<noteq> xc"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ex_new_if_finite finite.insertI infinite_UNIV_nat insertCI some_eq_ex someI_ex)

lemma getnewid_diffad:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xa \<noteq> xd"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ex_new_if_finite finite.insertI infinite_UNIV_nat insertCI some_eq_ex someI_ex)

lemma getnewid_diffbc:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xb \<noteq> xc"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ex_new_if_finite finite.insertI infinite_UNIV_nat insertCI some_eq_ex someI_ex)

lemma getnewid_diffbd:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xb \<noteq> xd"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ex_new_if_finite finite.insertI infinite_UNIV_nat insertCI some_eq_ex someI_ex)

lemma getnewid_diffcd:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xc \<noteq> xd"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ex_new_if_finite finite.insertI infinite_UNIV_nat insertCI some_eq_ex someI_ex)

lemma getnewid_diff1:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid ids) \<Longrightarrow>
  xb = fst (snd (getnewid ids)) \<Longrightarrow>
  xc = fst (snd (snd (getnewid ids))) \<Longrightarrow>
  xd = fst (snd (snd (snd (getnewid ids)))) \<Longrightarrow>
  xa \<noteq> xb \<and> xa \<noteq> xc \<and> xa \<noteq> xd"
  by (meson getnewid_diffab getnewid_diffac getnewid_diffad)

lemma getnewid_diff2:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid ids) \<Longrightarrow>
  xb = fst (snd (getnewid ids)) \<Longrightarrow>
  xc = fst (snd (snd (getnewid ids))) \<Longrightarrow>
  xd = fst (snd (snd (snd (getnewid ids)))) \<Longrightarrow>
  xb \<noteq> xc \<and> xb \<noteq> xd \<and> xc \<noteq> xd"
  by (meson getnewid_diffbc getnewid_diffbd getnewid_diffcd)

lemma getnewid_anot:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xa \<notin> ids"
  unfolding getnewid_def Let_def
  apply auto
  by (metis Collect_mem_eq finite_Collect_not infinite_UNIV_nat not_finite_existsD someI_ex)

lemma getnewid_bnot:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xb \<notin> ids"
  unfolding getnewid_def Let_def
  apply auto
  by (metis (mono_tags, lifting) finite_nat_set_iff_bounded lessI less_irrefl not_add_less2 plus_nat.simps(2) someI_ex)

lemma getnewid_cnot:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xc \<notin> ids"
  unfolding getnewid_def Let_def
  apply auto
  by (smt finite.insertI finite_nat_set_iff_bounded insert_compr less_irrefl mem_Collect_eq someI_ex)

lemma getnewid_dnot:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xd \<notin> ids"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ball_empty empty_Collect_eq ex_new_if_finite finite.insertI infinite_UNIV_nat insert_compr mem_Collect_eq some_eq_ex)

lemma getnewid_notbelong:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid ids) \<Longrightarrow>
  xb = fst (snd (getnewid ids)) \<Longrightarrow>
  xc = fst (snd (snd (getnewid ids))) \<Longrightarrow>
  xd = fst (snd (snd (snd (getnewid ids)))) \<Longrightarrow>
  xa \<notin> ids \<and> xb \<notin> ids \<and> xc \<notin> ids \<and> xd \<notin> ids"
  by (simp add: getnewid_anot getnewid_bnot getnewid_cnot getnewid_dnot)

definition divide :: "Block \<Rightarrow> ID set \<Rightarrow> (Block \<times> ID set)"
  where "divide bl ids \<equiv>
         (let b = L bl;
              nids = getnewid ids;
              x1 = fst nids;
              x2 = fst (snd nids);
              x3 = fst (snd (snd nids));
              x4 = fst (snd (snd (snd nids)));
              newids = snd (snd (snd (snd nids))) in                              
         (Node (Leaf (ALLOC, x1)) (Leaf (FREE, x2)) (Leaf (FREE, x3)) (Leaf (FREE, x4)), newids))"

lemma divide_diff:
  "finite ids \<Longrightarrow>
  fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd ll \<noteq> snd lr \<and> snd ll \<noteq> snd rl \<and> snd ll \<noteq> snd rr"
  unfolding divide_def Let_def using getnewid_diff1 by auto

lemma divide_diff2:
  "finite ids \<Longrightarrow>
  fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd lr \<noteq> snd rl \<and> snd lr \<noteq> snd rr \<and> snd rl \<noteq> snd rr"
  unfolding divide_def Let_def using getnewid_diff2 by auto

lemma divide_belong:
  "fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd ll \<in> snd (divide b ids) \<and>
  snd lr \<in> snd (divide b ids) \<and>
  snd rl \<in> snd (divide b ids) \<and>
  snd rr \<in> snd (divide b ids)"
  unfolding divide_def Let_def
  using newid1_in_getnewid newid2_in_getnewid newid3_in_getnewid newid4_in_getnewid by auto

lemma divide_notbelong:
  "finite ids \<Longrightarrow>
  fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd ll \<notin> ids \<and> snd lr \<notin> ids \<and> snd rl \<notin> ids \<and> snd rr \<notin> ids"
  unfolding divide_def Let_def using getnewid_notbelong by auto

lemma divide_finite:
  "finite ids \<Longrightarrow>
  finite (snd (divide b ids))"
proof-
  assume a0: "finite ids"
  have p0: "snd (divide b ids) = snd (snd (snd (snd (getnewid ids))))"
    unfolding divide_def Let_def by auto
  obtain xa xb xc xd
    where obtain_divide: "snd (divide b ids) = ids \<union> {xa, xb, xc, xd}"
    using p0 exists_p_getnewid by (metis sndI)
  have "finite (ids \<union> {xa, xb, xc, xd})" using a0 by auto
  then show ?thesis using obtain_divide by auto
qed

definition getnewid2 :: "ID set \<Rightarrow> (ID \<times> ID set)"
  where "getnewid2 ids \<equiv> let nid = SOME p. p \<notin> ids;
                             nids = ids \<union> {nid} in
                             (nid, nids)"

lemma getnewid2_inc: "ids \<subseteq> snd(getnewid2 ids)"
  unfolding getnewid2_def Let_def by auto

lemma newid_in_getnewid2: "fst(getnewid2 ids) \<in> snd(getnewid2 ids)"
  unfolding getnewid2_def Let_def by auto

lemma exists_p_getnewid2: "\<exists>p. getnewid2 ids = (p, ids \<union> {p})"
  unfolding getnewid2_def by metis

lemma getnewid2_anot:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid2 ids) \<Longrightarrow>
  xa \<notin> ids"
  unfolding getnewid2_def Let_def
  apply auto
  by (metis Collect_mem_eq finite_Collect_not infinite_UNIV_char_0 not_finite_existsD someI_ex)

definition combine :: "Block \<Rightarrow> ID set \<Rightarrow> (Block \<times> ID set)"
  where "combine b ids \<equiv> (if (\<exists>a1 a2 a3 a4. b = Node (Leaf (FREE, a1)) (Leaf (FREE, a2)) (Leaf (FREE, a3)) (Leaf (FREE, a4))) then
                              let nids = getnewid2 ids;
                                  newid = fst nids;
                                  newids = snd nids in (Leaf (FREE, newid), newids)
                           else (b, ids))"

lemma combine_ids:
  "ids \<subseteq> snd (combine b ids)"
  unfolding combine_def Let_def
  using getnewid2_inc by auto

lemma combine_finite:
  "finite ids \<Longrightarrow>
  finite (snd (combine b ids))"
  unfolding combine_def Let_def apply auto
  using exists_p_getnewid2 snd_conv
  by (metis Un_insert_right finite_insert sup_bot.right_neutral)

definition freesets :: "Block \<Rightarrow> Block set"
  where "freesets b = {l. leaf l \<and> L l \<in> set b \<and> fst (L l) = FREE}"

definition freesets_level :: "Block \<Rightarrow> nat \<Rightarrow> Block set"
  where "freesets_level b lv = {l. l \<in> freesets b \<and> get_level b (L l) = lv}"

definition freesets_level_pool :: "Block set \<Rightarrow> nat \<Rightarrow> Block set"
  where "freesets_level_pool bset lv = {l. \<exists>b \<in> bset. l \<in> freesets_level b lv}"

definition freesets_maxlevel :: "Block set \<Rightarrow> nat \<Rightarrow> nat"
  where "freesets_maxlevel bset lv \<equiv>
          THE lmax. lmax \<le> lv \<and>
                    freesets_level_pool bset lmax \<noteq> {} \<and>
                    (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"

definition exists_freelevel :: "Block set \<Rightarrow> nat \<Rightarrow> bool"
  where "exists_freelevel bset lv \<equiv> \<exists>lv'. lv' \<le> lv \<and> freesets_level_pool bset lv' \<noteq> {}"

lemma exist_lmax_h:
  "freesets_level_pool bset lv = {} \<Longrightarrow>
  \<exists>lv'. lv' < lv \<and> freesets_level_pool bset lv' \<noteq> {} \<Longrightarrow>
  \<exists>lmax. lmax < lv \<and>
         freesets_level_pool bset lmax \<noteq> {} \<and>
         (\<forall>l. l \<le> lv \<and> l > lmax \<longrightarrow> freesets_level_pool bset l = {})"
proof(induct lv)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  then show ?case
    by (smt Suc_leI Suc_le_lessD le_Suc_eq lessI not_less)
qed

lemma exist_lmax:
  "exists_freelevel bset lv \<Longrightarrow>
  \<exists>!lmax. lmax \<le> lv \<and>
          freesets_level_pool bset lmax \<noteq> {} \<and>
          (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
proof-
  assume exi_level: "exists_freelevel bset lv"
  hence exi_level_def: "\<exists>lv'. lv' \<le> lv \<and> freesets_level_pool bset lv' \<noteq> {}"
    unfolding exists_freelevel_def by auto
  {assume a0: "freesets_level_pool bset lv \<noteq> {}"
    hence "lv \<le> lv \<and>
          freesets_level_pool bset lv \<noteq> {} \<and>
          (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lv)"
      using exi_level_def by auto
    then have ?thesis using le_antisym by blast
  }moreover
  {assume a1: "freesets_level_pool bset lv = {}"
    hence exi_level_less: "\<exists>lv'. lv' < lv \<and> freesets_level_pool bset lv' \<noteq> {}"
      using exi_level_def le_neq_implies_less by blast
    have "\<exists>lmax. lmax < lv \<and>
                 freesets_level_pool bset lmax \<noteq> {} \<and>
                 (\<forall>l. l \<le> lv \<and> l > lmax \<longrightarrow> freesets_level_pool bset l = {})"
      using exist_lmax_h a1 exi_level_less by auto
    then obtain lmax where exi_lmax:
      "lmax < lv \<and>
      freesets_level_pool bset lmax \<noteq> {} \<and>
      (\<forall>l. l \<le> lv \<and> l > lmax \<longrightarrow> freesets_level_pool bset l = {})" by auto
    then have "\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax"
      using a1 by (metis le_less_linear)
    then have ?thesis using exi_lmax
      by (meson le_less_Suc_eq le_simps(2) less_imp_le_nat)
  }
  ultimately have ?thesis by linarith
  then show ?thesis by auto
qed

subsection \<open>def of sub core function\<close>
(*------------------------------------------------------------------------------------------------*)
definition set_state_type :: "Block \<Rightarrow> block_state_type \<Rightarrow> Block"
  where "set_state_type bl t \<equiv> (let b = (L bl) in Leaf (t, snd b))"

definition replace :: "Block \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> Block"
  where "replace B b b' \<equiv> (tree_map (\<lambda>b1. if (b1 = L b) then (L b') else b1) B)"

lemma no_replace:
  "L b \<notin> set blo \<Longrightarrow>
  b' = set_state_type b t \<Longrightarrow>
  tree_map (\<lambda>b1. if b1 = L b then L b' else b1) blo = blo"
  by (smt tree.map_cong0 tree.map_ident)

fun split :: "Block \<Rightarrow> ID set \<Rightarrow> nat \<Rightarrow> (Block \<times> ID set)"
  where "split b ids lv = (if lv = 0 then (b, ids)
                          else
                            let re = divide b ids;
                                node = fst re;
                                newids = snd re;
                                c1 = split (LL node) newids (lv - 1) in
                                (Node (fst c1) (LR node) (RL node) (RR node), snd c1))"

lemma split_induct:
  "lv > 0 \<Longrightarrow>
  fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newids = snd (divide b ids) \<Longrightarrow>
  fst (split b ids lv) = Node (fst (split (Leaf ll) newids (lv - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
  using split.simps unfolding Let_def
  by (metis fst_conv less_not_refl3 tree.sel(2) tree.sel(3) tree.sel(4) tree.sel(5))

fun replace_leaf :: "Block \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> Block"
  where "replace_leaf (Leaf x) y st = (if (x = (L y)) then st else (Leaf x))" |
        "replace_leaf (Node n1 n2 n3 n4) y st = Node (replace_leaf n1 y st)
                                                     (replace_leaf n2 y st)
                                                     (replace_leaf n3 y st)
                                                     (replace_leaf n4 y st)"

lemma no_replace_leaf:
  "(L b) \<notin> set B \<Longrightarrow>
  replace_leaf B b subbtr = B"
  apply(induct B)
  by auto

lemma replace_leaf_belong:
  "(L b) \<in> set B \<Longrightarrow>
  (L l) \<in> set subbtr \<Longrightarrow>
  (L l) \<in> set (replace_leaf B b subbtr)"
  apply(induct B)
  by auto

lemma replace_subbtr_belong:
  "(L b) \<in> set B \<Longrightarrow>
  tree.set subbtr \<subseteq> tree.set (replace_leaf B b subbtr)"
  apply(induct B)
  by auto

fun merge :: "Block \<Rightarrow> ID set \<Rightarrow> (Block \<times> ID set)"
  where "merge (Leaf v) ids = ((Leaf v), ids)" |
        "merge (Node ll lr rl rr) ids =
                (if (\<exists>xa xb xc xd. (Node ll lr rl rr) = Node (Leaf (FREE, xa))
                                                             (Leaf (FREE, xb))
                                                             (Leaf (FREE, xc))
                                                             (Leaf (FREE, xd)))
                 then combine (Node ll lr rl rr) ids
                 else
                    let m1 = merge ll ids;
                        m2 = merge lr (snd m1);
                        m3 = merge rl (snd m2);
                        m4 = merge rr (snd m3) in
                    combine (Node (fst m1) (fst m2) (fst m3) (fst m4)) (snd m4))"

definition alloc1 :: "Block set \<Rightarrow> nat \<Rightarrow> ID set \<Rightarrow> (Block set \<times> ID set \<times> bool)"
  where "alloc1 bset lv ids \<equiv> (let blo = (SOME b. b \<in> bset \<and> freesets_level b lv \<noteq> {});
                                   b = (SOME l. l \<in> freesets_level blo lv);
                                   newblo = replace blo b (set_state_type b ALLOC) in
                              ((bset - {blo}) \<union> {newblo}, ids, True))"

definition alloc :: "Block set \<Rightarrow> nat \<Rightarrow> ID set \<Rightarrow> (Block set \<times> ID set \<times> bool)"
  where "alloc bset lv ids \<equiv>
         if (exists_freelevel bset lv) then
            let lmax = freesets_maxlevel bset lv in
                if lmax = lv then
                   alloc1 bset lv ids
                else                                   
                   let blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {});
                       b = (SOME l. l \<in> freesets_level blo lmax);
                       re = split b ids (lv - lmax);
                       subbtr = fst re;
                       newids = snd re;
                       newbtr = replace_leaf blo b subbtr in
                   (((bset - {blo}) \<union> {newbtr}), newids, True)
         else (bset, ids, False)"

definition free :: "Block set \<Rightarrow> Block \<Rightarrow> ID set \<Rightarrow> (Block set \<times> ID set \<times> bool)"
  where "free bset b ids \<equiv>
         if (\<exists>btree \<in> bset. (L b) \<in> set btree) then
            if fst (L b) = FREE then
                (bset, ids, False)
            else
                let btree = (THE t. t \<in> bset \<and> (L b) \<in> set t);
                    freeblo = replace btree b (set_state_type b FREE);
                    re = merge freeblo ids;
                    newblo = fst re;
                    newids = snd re in
                ((bset - {btree}) \<union> {newblo}, newids, True)
         else
            (bset, ids, False)"

end