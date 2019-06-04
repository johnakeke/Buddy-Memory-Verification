theory Memory_Allocation_Model
imports Main
begin

subsection \<open>def of datetype\<close>
(*------------------------------------------------------------------------------------------------*)
datatype (set: 'a) tree = leaf: Leaf (L: 'a) |
                          node: Node (LL:"'a tree") (LR:"'a tree") (RL:"'a tree") (RR:"'a tree")
                        for map: tree_map   

definition replace :: "'a tree \<Rightarrow>'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  where "replace B b b' \<equiv> (tree_map (\<lambda>b1. if (b1 = L b) then (L b') else b1) B)"




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
inductive id_not_in_mem :: "Block \<Rightarrow> ID \<Rightarrow> bool"
  where id_not_in_leaf: "snd a \<noteq> v \<Longrightarrow> id_not_in_mem (Leaf a) v" |
        id_not_in_Node: "id_not_in_mem ll v \<and> id_not_in_mem lr v \<and> id_not_in_mem rl v \<and> id_not_in_mem rr v
                \<Longrightarrow> id_not_in_mem (Node ll lr rl rr) v"
inductive_cases id_not_in_mem_node:
  "id_not_in_mem (Node ll lr rl rr) v"

definition id_not_in_set_mem::"Block set \<Rightarrow> ID \<Rightarrow> bool"
  where "id_not_in_set_mem bs v \<equiv> \<forall>b \<in> bs. id_not_in_mem b v"

lemma finite_ids_set:"finite (snd ` set b)"
proof (induct b)
  case (Leaf x)
  then show ?case
    using id_not_in_mem.cases by auto 
next
  case (Node b1 b2 b3 b4)
  then show ?case
    by (simp add: image_Un)  
qed

lemma finite_ids_set_set:"finite bs \<Longrightarrow> bs\<noteq>{} \<Longrightarrow> finite (\<Union>b\<in>bs. (snd ` set b))"
proof (induct bs rule:finite_induct)
case empty
  then show ?case by auto
next
  case (insert x F) 
  then show ?case
  proof(cases F)
    case emptyI
    then show ?thesis using finite_ids_set by auto
  next
    case (insertI A a)
    then have "finite (\<Union>b\<in>F. snd ` tree.set b)" using insert by auto
    moreover have "finite (snd ` tree.set x)" using finite_ids_set by auto
    ultimately show ?thesis by auto
  qed
qed

lemma not_in_mem_not_in_set1:"id_not_in_mem b v \<Longrightarrow> v \<notin> snd ` set b"
proof (induct b)
  case (Leaf x)
  then show ?case
    using id_not_in_mem.cases by auto 
next
  case (Node b1 b2 b3 b4)
  then show ?case using id_not_in_mem_node
    by (metis UnE image_Un tree.simps(16)) 
qed

lemma not_in_mem_not_in_set2:"v \<notin> snd ` set b \<Longrightarrow> id_not_in_mem b v "
proof (induct b)
  case (Leaf x)
  then show ?case    
    by (simp add: id_not_in_leaf) 
next
  case (Node b1 b2 b3 b4)
  then show ?case using id_not_in_mem_node
    by (simp add: id_not_in_Node image_Un)
qed

lemma not_in_mem_not_in_set:"v \<notin> snd ` set b = id_not_in_mem b v "
  using  not_in_mem_not_in_set1 not_in_mem_not_in_set2 by auto

lemma  not_in_mem_set_not_in_set_set:
"finite bs \<Longrightarrow> bs\<noteq>{} \<Longrightarrow> (v \<notin> (\<Union>b\<in>bs. (snd ` set b))) = id_not_in_set_mem bs v "
proof(induct bs rule:finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then show ?case using not_in_mem_not_in_set unfolding id_not_in_set_mem_def
    by (meson UN_iff)    
qed


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



lemma exists_set_not_in_P:
"\<not> (finite (UNIV::'a set)) \<Longrightarrow> finite (P::'a set) \<Longrightarrow> \<exists>s. finite s \<and> card s = n \<and> (s \<inter> P = {})"
proof(induct n )
case 0
then show ?case
  using card_empty by blast 
next
  case (Suc n)
  then obtain s where "finite s \<and> card s = n \<and> s \<inter> P = {}" by auto
  moreover have "s \<union> P \<noteq> UNIV" using Suc(2,3) calculation by (metis infinite_Un)
  then obtain v where "v \<notin> s \<union> P"  by auto
  ultimately show ?case
    by (metis Int_insert_left UnI1 UnI2 card_insert_disjoint finite_insert)
qed



definition divide:: "ID set \<Rightarrow> Block set"
  where "divide  ids \<equiv>
         let ids1 = {s. (card s = 4 \<and> s \<inter> ids = {})} in             
         {n. (\<exists>s x1 x2 x3 x4. s \<in> ids1 \<and>
                              x1 \<in> s \<and> x2 \<in> s - {x1} \<and> x3 \<in> s - {x1,x2} \<and> x4 \<in> s -{x1,x2,x3} \<and>
               n = (Node (Leaf (ALLOC, x1)) (Leaf (FREE, x2)) (Leaf (FREE, x3)) (Leaf (FREE, x4))))}                
         "

lemma exist_s_card_n:"\<not> (finite (UNIV::'b set)) \<Longrightarrow> 
        finite (bs::('a \<times> 'b) tree set) \<Longrightarrow> 
         bs\<noteq>{} \<Longrightarrow> 
         \<exists>s. (card s = n \<and> s \<inter> (\<Union>b\<in>bs. (snd ` set b)) = {})"
  using finite_ids_set_set exists_set_not_in_P by metis
  
lemma diff_set_not_empty:"card s = n \<Longrightarrow>
       finite s' \<Longrightarrow>
       card s' <n \<Longrightarrow>
       (s - s') \<noteq>{}"
  using card_mono not_less by auto
  
lemma elem_in_diff_set:"card s = n \<Longrightarrow>
       finite s' \<Longrightarrow>
       card s' <n \<Longrightarrow> \<exists>x.  x\<in> s - s'"
  by (meson all_not_in_conv diff_set_not_empty)

lemma assumes a0:"finite ids"      
  shows "divide ids \<noteq> {}"
proof-
   obtain s where s:"((card s = 4 \<and> s \<inter> ids = {}))"
    using exists_set_not_in_P a0
    by (metis infinite_UNIV_nat)
  obtain x1 where x1_in_s:"x1 \<in> s" using elem_in_diff_set s by fastforce    
  moreover obtain x2 where x2_in_s:"x2 \<in> s - {x1}" using elem_in_diff_set[of s _ "{x1}"] by (auto simp: s)
  moreover  obtain x3 where x3_in_s:"x3 \<in> s - {x1, x2}" using 
    calculation elem_in_diff_set[of s _ "{x1,x2}"] by (auto simp: s)  
  moreover obtain x4 where x4_in_s:"x4 \<in> s - {x1, x2,x3}" using s 
    elem_in_diff_set[of s _ "{x1,x2,x3}"]  calculation
    by  (auto simp: s)
  ultimately have "card {x1,x2,x3,x4} = 4" by auto
  then show ?thesis
    unfolding divide_def Let_def 
    using s x1_in_s x2_in_s x3_in_s x4_in_s apply auto   by metis    
qed  

lemma divide_dest1:assumes a0:"finite ids" 
  shows "\<forall>node\<in> divide ids. snd ` set node \<inter> ids = {}"
proof-   
  let ?ids = "{s. (card s = 4 \<and> s \<inter> ids = {})}" 
  { 
    fix node
    assume a00:"node \<in> divide ids"
    then obtain s x1 x2 x3 x4 where 
       spec:"s \<in> ?ids \<and> x1 \<in> s \<and> x2 \<in> s - {x1} \<and> x3 \<in> s - {x1,x2} \<and> x4 \<in> s -{x1,x2,x3} \<and>
        node = (Node (Leaf (ALLOC, x1)) (Leaf (FREE, x2)) (Leaf (FREE, x3)) (Leaf (FREE, x4)))"
      unfolding divide_def by auto    
    then have "snd ` set node \<inter> ids = {}"
      by auto
  } thus ?thesis by auto
qed

lemma divide_dest2:assumes a0:"finite ids" 
  shows "\<forall>node\<in> divide ids. card (set node) = 4"
proof-   
  let ?ids = "{s. (card s = 4 \<and> s \<inter> ids = {})}" 
  { 
    fix node
    assume a00:"node \<in> divide ids"
    then obtain s x1 x2 x3 x4 where 
       spec:"s \<in> ?ids \<and> x1 \<in> s \<and> x2 \<in> s - {x1} \<and> x3 \<in> s - {x1,x2} \<and> x4 \<in> s -{x1,x2,x3} \<and>
        node = (Node (Leaf (ALLOC, x1)) (Leaf (FREE, x2)) (Leaf (FREE, x3)) (Leaf (FREE, x4)))"
      unfolding divide_def by auto    
    then have "card (set node) = 4"
      by auto
  } thus ?thesis by auto
qed

lemma divide_dest3:assumes a0:"finite ids" and 
   a2: "(Node n1 n2 n3 n4) \<in> divide ids"
 shows "leaf n1 \<and> leaf n2 \<and> leaf n3 \<and> leaf n4 \<and>
        snd (L n1) \<noteq> snd (L n2) \<and> snd (L n1) \<noteq> snd (L n3) \<and> snd (L n1) \<noteq> snd (L n4) \<and> 
        snd (L n2) \<noteq> snd (L n1) \<and> snd (L n2) \<noteq> snd (L n3) \<and> snd (L n3)\<noteq> snd (L n4)"
proof-   
  let ?ids = "{s. (card s = 4 \<and> s \<inter> ids = {})}" 
  let ?node = "(Node n1 n2 n3 n4)"
   obtain s x1 x2 x3 x4 where 
       spec:"s \<in> ?ids \<and> x1 \<in> s \<and> x2 \<in> s - {x1} \<and> x3 \<in> s - {x1,x2} \<and> x4 \<in> s -{x1,x2,x3} \<and>
        ?node = (Node (Leaf (ALLOC, x1)) (Leaf (FREE, x2)) (Leaf (FREE, x3)) (Leaf (FREE, x4)))"
      using a2 unfolding divide_def by auto    
    then have "leaf n1 \<and> leaf n2 \<and> leaf n3 \<and> leaf n4 \<and>
        snd (L n1) \<noteq> snd (L n2) \<and> snd (L n1) \<noteq> snd (L n3) \<and> snd (L n1) \<noteq> snd (L n4) \<and> 
        snd (L n2) \<noteq> snd (L n1) \<and> snd (L n2) \<noteq> snd (L n3) \<and> snd (L n3)\<noteq> snd (L n4)"
      by auto
  thus ?thesis by auto
qed

   
(* definition divide :: "Block \<Rightarrow> ID set \<Rightarrow> (Block \<times> ID set)"
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
  unfolding divide_def Let_def ID setusing getnewid_diff1 by auto

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
*)
definition getnewid2 :: "Block set \<Rightarrow> ID"
  where "getnewid2 bs \<equiv> SOME p. p \<notin> (\<Union>b\<in>bs. (snd ` set b))"

  
lemma fresh_elem:"\<not> (finite (UNIV::'b set)) \<Longrightarrow> finite (bs::('a \<times> 'b) tree set) \<Longrightarrow> 
                   bs\<noteq>{} \<Longrightarrow> \<exists>p . p \<notin> (\<Union>b\<in>bs. (snd ` set b))"
  using ex_new_if_finite finite_ids_set_set
  by blast 

lemma newid_in_getnewid2: "getnewid2 bs \<in> (\<Union>b\<in>bs. (snd ` set b)) \<union> {(getnewid2 bs)}"
  unfolding getnewid2_def Let_def by auto

lemma getnewid2_anot:
  "finite bs \<Longrightarrow> bs\<noteq>{} \<Longrightarrow>
  xa = (getnewid2 bs) \<Longrightarrow>
  xa \<notin> (\<Union>b\<in>bs. (snd ` set b))"
  unfolding getnewid2_def Let_def
  using fresh_elem
  by (metis infinite_UNIV_nat some_eq_ex)

definition combine :: "Block \<Rightarrow> Block set \<Rightarrow> Block"
  where "combine b bs \<equiv> (if (\<exists>a1 a2 a3 a4. b = Node (Leaf (FREE, a1)) (Leaf (FREE, a2)) (Leaf (FREE, a3)) (Leaf (FREE, a4))) then
                              (Leaf (FREE, getnewid2 bs))
                           else b)"

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


fun split :: "Block \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> Block"
  where "split b ids lv = (if lv = 0 then b
                          else
                            let  node = SOME l. l \<in> divide ids;                                
                                c1 = split (LL node) (ids \<union> (snd ` (set node))) (lv - 1) in
                                Node c1 (LR node) (RL node) (RR node))"

lemma split_induct:
  "lv > 0 \<Longrightarrow>
  Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<in> (divide bs)  \<Longrightarrow>  
  (split b bs lv) = Node ((split (Leaf ll) bs (lv - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
  using split.simps unfolding Let_def sorry
  by (metis fst_conv less_not_refl3 tree.sel(2) tree.sel(3) tree.sel(4) tree.sel(5))

fun replace_leaf :: "Block \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> Block"
  where "replace_leaf (Leaf x) y st = (if (x = (L y)) then st else (Leaf x))" |
        "replace_leaf (Node n1 n2 n3 n4) y st = Node (replace_leaf n1 y st)
                                                     (replace_leaf n2 y st)
                                                     (replace_leaf n3 y st)
                                                     (replace_leaf n4 y st)"
lemma no_replace:
  "L b \<notin> set blo \<Longrightarrow>
  b' = set_state_type b t \<Longrightarrow>
  tree_map (\<lambda>b1. if b1 = L b then L b' else b1) blo = blo"
  by (smt tree.map_cong0 tree.map_ident)

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

fun merge :: "Block \<Rightarrow> Block set \<Rightarrow> Block"
  where "merge (Leaf v) bs = (Leaf v)" |
        "merge (Node ll lr rl rr) bs =
                (if (\<exists>xa xb xc xd. (Node ll lr rl rr) = Node (Leaf (FREE, xa))
                                                             (Leaf (FREE, xb))
                                                             (Leaf (FREE, xc))
                                                             (Leaf (FREE, xd)))
                 then combine (Node ll lr rl rr) bs
                 else
                    let m1 = merge ll bs;
                        m2 = merge lr bs;
                        m3 = merge rl bs;
                        m4 = merge rr bs in
                    combine (Node m1 m2 m3 m3) bs)"

definition alloc1 :: "Block set \<Rightarrow> nat \<Rightarrow>  (Block set \<times>  bool)"
  where "alloc1 bset lv  \<equiv> (let blo = (SOME b. b \<in> bset \<and> freesets_level b lv \<noteq> {});
                                   b = (SOME l. l \<in> freesets_level blo lv);
                                   allocid = snd (L b);
                                   newblo = replace blo b (set_state_type b ALLOC) in
                              ((bset - {blo}) \<union> {newblo}, True))"

definition alloc :: "Block set \<Rightarrow> nat \<Rightarrow>  (Block set \<times> bool)"
  where "alloc bset lv  \<equiv>
         if (exists_freelevel bset lv) then
            let lmax = freesets_maxlevel bset lv in
                if lmax = lv then
                   alloc1 bset lv 
                else
                   let blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {});
                       b = (SOME l. l \<in> freesets_level blo lmax);                                              
                       newbtr = replace_leaf blo b (split b (\<Union>b\<in>bset. (snd ` set b)) (lv - lmax)) in
                   (((bset - {blo}) \<union> {newbtr}), True)
         else (bset, False)"

definition free :: "Block set \<Rightarrow> Block \<Rightarrow>(Block set \<times> bool)"
  where "free bset b  \<equiv>
         if (\<exists>btree \<in> bset. (L b) \<in> set btree) then
            if fst (L b) = FREE then
                (bset, False)
            else
                let btree = (THE t. t \<in> bset \<and> (L b) \<in> set t);
                    freeblo = replace btree b (set_state_type b FREE) in
                ((bset - {btree}) \<union> {merge freeblo bset}, True)
         else
            (bset, False)"

end