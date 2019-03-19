theory Memory_Allocation_Invariant
imports Memory_Allocation_Model
begin

subsection \<open>def and proof of inv_different_ids\<close>

definition id_set :: "Block \<Rightarrow> ID set"
  where "id_set b \<equiv> set (tree_map snd b)"

lemma id_set_node:
  "id_set (Node b1 b2 b3 b4) = id_set b1 \<union> id_set b2 \<union> id_set b3 \<union> id_set b4"
  unfolding id_set_def by auto

lemma id_set_notempty: "id_set B \<noteq> {}"
  apply(induct B)
  unfolding id_set_def apply auto[1]
  using id_set_node unfolding id_set_def by auto

inductive diff_ids:: "Block \<Rightarrow> bool"
  where diff1: "diff_ids (Leaf a)" |
        diff2: "(id_set b1) \<inter> (id_set b2) = {} \<and> (id_set b1) \<inter> (id_set b3) = {} \<and> (id_set b1) \<inter> (id_set b4) = {} \<and>
                (id_set b2) \<inter> (id_set b3) = {} \<and> (id_set b2) \<inter> (id_set b4) = {} \<and>
                (id_set b3) \<inter> (id_set b4) = {} \<and>
                diff_ids b1 \<and> diff_ids b2 \<and> diff_ids b3 \<and> diff_ids b4 \<Longrightarrow> diff_ids (Node b1 b2 b3 b4)"

inductive_cases diff_ids_leaf_node:
  "diff_ids (Leaf a)"
  "diff_ids (Node ll lr rl rr)"

lemma diff_leaf1:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  (L l) \<in> set b1 \<Longrightarrow>
  (L l) \<notin> set b2 \<and> (L l) \<notin> set b3 \<and> (L l) \<notin> set b4"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "(L l) \<in> set b1"
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have l_id: "snd (L l) \<in> id_set b1"
    unfolding id_set_def using a1
    by (simp add: tree.set_map) 
  have n1: "snd (L l) \<notin> id_set b2"
    using diff_ab l_id by auto
  have n2: "snd (L l) \<notin> id_set b3"
    using diff_ac l_id by auto
  have n3: "snd (L l) \<notin> id_set b4"
    using diff_ad l_id by auto
  show ?thesis using n1 n2 n3
    using id_set_def tree.set_map by fastforce 
qed

lemma diff_leaf2:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  (L l) \<in> set b2 \<Longrightarrow>
  (L l) \<notin> set b1 \<and> (L l) \<notin> set b3 \<and> (L l) \<notin> set b4"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "(L l) \<in> set b2"
  have diff_ab: "(id_set b2) \<inter> (id_set b1) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have l_id: "snd (L l) \<in> id_set b2"
    unfolding id_set_def using a1
    by (simp add: tree.set_map) 
  have n1: "snd (L l) \<notin> id_set b1"
    using diff_ab l_id by auto
  have n2: "snd (L l) \<notin> id_set b3"
    using diff_bc l_id by auto
  have n3: "snd (L l) \<notin> id_set b4"
    using diff_bd l_id by auto
  show ?thesis using n1 n2 n3
    using id_set_def tree.set_map by fastforce 
qed

lemma diff_leaf3:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  (L l) \<in> set b3 \<Longrightarrow>
  (L l) \<notin> set b1 \<and> (L l) \<notin> set b2 \<and> (L l) \<notin> set b4"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "(L l) \<in> set b3"
  have diff_ac: "(id_set b3) \<inter> (id_set b1) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b3) \<inter> (id_set b2) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have l_id: "snd (L l) \<in> id_set b3"
    unfolding id_set_def using a1
    by (simp add: tree.set_map) 
  have n1: "snd (L l) \<notin> id_set b1"
    using diff_ac l_id by auto
  have n2: "snd (L l) \<notin> id_set b2"
    using diff_bc l_id by auto
  have n3: "snd (L l) \<notin> id_set b4"
    using diff_cd l_id by auto
  show ?thesis using n1 n2 n3
    using id_set_def tree.set_map by fastforce 
qed

lemma diff_leaf4:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  (L l) \<in> set b4 \<Longrightarrow>
  (L l) \<notin> set b1 \<and> (L l) \<notin> set b2 \<and> (L l) \<notin> set b3"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "(L l) \<in> set b4"
  have diff_ad: "(id_set b4) \<inter> (id_set b1) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b4) \<inter> (id_set b2) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b4) \<inter> (id_set b3) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have l_id: "snd (L l) \<in> id_set b4"
    unfolding id_set_def using a1
    by (simp add: tree.set_map) 
  have n1: "snd (L l) \<notin> id_set b1"
    using diff_ad l_id by auto
  have n2: "snd (L l) \<notin> id_set b2"
    using diff_bd l_id by auto
  have n3: "snd (L l) \<notin> id_set b3"
    using diff_cd l_id by auto
  show ?thesis using n1 n2 n3
    using id_set_def tree.set_map by fastforce 
qed 

lemma diff_node1:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  tree.set subbtr \<subseteq> tree.set b1 \<Longrightarrow>
  \<not> tree.set subbtr \<subseteq> tree.set b2 \<and> \<not> tree.set subbtr \<subseteq> tree.set b3 \<and> \<not> tree.set subbtr \<subseteq> tree.set b4"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "tree.set subbtr \<subseteq> tree.set b1"
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have subbtr_id: "id_set subbtr \<subseteq> id_set b1"
    unfolding id_set_def using a1
    by (metis subset_image_iff tree.set_map)
  have n1: "\<not> id_set subbtr \<subseteq> id_set b2"
    using diff_ab subbtr_id id_set_notempty by fastforce
  have n2: "\<not> id_set subbtr \<subseteq> id_set b3"
    using diff_ac subbtr_id id_set_notempty by fastforce
  have n3: "\<not> id_set subbtr \<subseteq> id_set b4"
    using diff_ad subbtr_id id_set_notempty by fastforce
  show ?thesis using n1 n2 n3 unfolding id_set_def
    by (metis subset_image_iff tree.set_map)
qed

lemma diff_node2:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  tree.set subbtr \<subseteq> tree.set b2 \<Longrightarrow>
  \<not> tree.set subbtr \<subseteq> tree.set b1 \<and> \<not> tree.set subbtr \<subseteq> tree.set b3 \<and> \<not> tree.set subbtr \<subseteq> tree.set b4"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "tree.set subbtr \<subseteq> tree.set b2"
  have diff_ab: "(id_set b2) \<inter> (id_set b1) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have subbtr_id: "id_set subbtr \<subseteq> id_set b2"
    unfolding id_set_def using a1
    by (metis subset_image_iff tree.set_map)
  have n1: "\<not> id_set subbtr \<subseteq> id_set b1"
    using diff_ab subbtr_id id_set_notempty by fastforce
  have n2: "\<not> id_set subbtr \<subseteq> id_set b3"
    using diff_bc subbtr_id id_set_notempty by fastforce
  have n3: "\<not> id_set subbtr \<subseteq> id_set b4"
    using diff_bd subbtr_id id_set_notempty by fastforce
  show ?thesis using n1 n2 n3 unfolding id_set_def
    by (metis subset_image_iff tree.set_map)
qed

lemma diff_node3:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  tree.set subbtr \<subseteq> tree.set b3 \<Longrightarrow>
  \<not> tree.set subbtr \<subseteq> tree.set b1 \<and> \<not> tree.set subbtr \<subseteq> tree.set b2 \<and> \<not> tree.set subbtr \<subseteq> tree.set b4"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "tree.set subbtr \<subseteq> tree.set b3"
  have diff_ac: "(id_set b3) \<inter> (id_set b1) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b3) \<inter> (id_set b2) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have subbtr_id: "id_set subbtr \<subseteq> id_set b3"
    unfolding id_set_def using a1
    by (metis subset_image_iff tree.set_map)
  have n1: "\<not> id_set subbtr \<subseteq> id_set b1"
    using diff_ac subbtr_id id_set_notempty by fastforce
  have n2: "\<not> id_set subbtr \<subseteq> id_set b2"
    using diff_bc subbtr_id id_set_notempty by fastforce
  have n3: "\<not> id_set subbtr \<subseteq> id_set b4"
    using diff_cd subbtr_id id_set_notempty by fastforce
  show ?thesis using n1 n2 n3 unfolding id_set_def
    by (metis subset_image_iff tree.set_map)
qed

lemma diff_node4:
  "diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  tree.set subbtr \<subseteq> tree.set b4 \<Longrightarrow>
  \<not> tree.set subbtr \<subseteq> tree.set b1 \<and> \<not> tree.set subbtr \<subseteq> tree.set b2 \<and> \<not> tree.set subbtr \<subseteq> tree.set b3"
proof-
  assume a0: "diff_ids (Node b1 b2 b3 b4)"
     and a1: "tree.set subbtr \<subseteq> tree.set b4"
  have diff_ad: "(id_set b4) \<inter> (id_set b1) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b4) \<inter> (id_set b2) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b4) \<inter> (id_set b3) = {}"
    using a0 diff_ids_leaf_node(2) by blast
  have subbtr_id: "id_set subbtr \<subseteq> id_set b4"
    unfolding id_set_def using a1
    by (metis subset_image_iff tree.set_map)
  have n1: "\<not> id_set subbtr \<subseteq> id_set b1"
    using diff_ad subbtr_id id_set_notempty by fastforce
  have n2: "\<not> id_set subbtr \<subseteq> id_set b2"
    using diff_bd subbtr_id id_set_notempty by fastforce
  have n3: "\<not> id_set subbtr \<subseteq> id_set b3"
    using diff_cd subbtr_id id_set_notempty by fastforce
  show ?thesis using n1 n2 n3 unfolding id_set_def
    by (metis subset_image_iff tree.set_map)
qed

definition "diff_ids_valid bset \<equiv> 
  (\<forall>b \<in> bset. diff_ids b) \<and> 
  (\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"

lemma same_ids_replace:
  "diff_ids B \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b t \<Longrightarrow>
  id_set B = id_set (replace B b b')"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(2) by auto
  have leaf_b': "b' = Leaf (t, snd x)"
    using Leaf.prems(3) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B': "replace (Leaf x) b b' = Leaf (t, snd x)"
    using leaf_b leaf_b' unfolding replace_def by auto
  then show ?case unfolding id_set_def by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(3) apply auto[1]
      using no_replace no_belong_b3 Node.prems(3) apply auto[1]
      using no_replace no_belong_b4 Node.prems(3) by auto
    have same_b1': "id_set b1 = id_set (replace b1 b b')"
      using Node.hyps(1) diff_b1 a0 Node.prems(3) by auto
    have ?case using replace_re id_set_node same_b1' by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(3) apply auto[1]
      using no_replace no_belong_b3 Node.prems(3) apply auto[1]
      using no_replace no_belong_b4 Node.prems(3) by auto
    have same_b2': "id_set b2 = id_set (replace b2 b b')"
      using Node.hyps(2) diff_b2 a1 Node.prems(3) by auto
    have ?case using replace_re id_set_node same_b2' by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(3) apply auto[1]
      using no_replace no_belong_b2 Node.prems(3) apply auto[1]
      using no_replace no_belong_b4 Node.prems(3) by auto
    have same_b3': "id_set b3 = id_set (replace b3 b b')"
      using Node.hyps(3) diff_b3 a2 Node.prems(3) by auto
    have ?case using replace_re id_set_node same_b3' by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(3) apply auto[1]
      using no_replace no_belong_b2 Node.prems(3) apply auto[1]
      using no_replace no_belong_b3 Node.prems(3) by auto
    have same_b4': "id_set b4 = id_set (replace b4 b b')"
      using Node.hyps(4) diff_b4 a3 Node.prems(3) by auto
    have ?case using replace_re id_set_node same_b4' by auto
  }
  ultimately have ?case using Node.prems(2) by fastforce
  then show ?case by auto
qed

lemma diff_ids_replace:
  "diff_ids B \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b t \<Longrightarrow>
  diff_ids (replace B b b')"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(2) by fastforce
  have leaf_b': "b' = Leaf (t, snd x)"
    using Leaf.prems(3) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B': "replace (Leaf x) b b' = Leaf (t, snd x)"
    using leaf_b leaf_b' unfolding replace_def by auto
  then show ?case using diff1 by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(3) apply auto[1]
      using no_replace no_belong_b3 Node.prems(3) apply auto[1]
      using no_replace no_belong_b4 Node.prems(3) by auto
    have diff_b1': "diff_ids (replace b1 b b')"
      using Node.hyps(1) diff_b1 a0 Node.prems(3) by auto
    have diff_ab': "id_set (replace b1 b b') \<inter> id_set b2 = {}"
      using same_ids_replace diff_b1 a0 Node.prems(3) diff_ab by auto
    have diff_ac': "id_set (replace b1 b b') \<inter> id_set b3 = {}"
      using same_ids_replace diff_b1 a0 Node.prems(3) diff_ac by auto
    have diff_ad': "id_set (replace b1 b b') \<inter> id_set b4 = {}"
      using same_ids_replace diff_b1 a0 Node.prems(3) diff_ad by auto
    have ?case using replace_re diff_b1' diff_b2 diff_b3 diff_b4 diff_ab' diff_ac' diff_ad' diff_bc diff_bd diff_cd diff2 by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(3) apply auto[1]
      using no_replace no_belong_b3 Node.prems(3) apply auto[1]
      using no_replace no_belong_b4 Node.prems(3) by auto
    have diff_b2': "diff_ids (replace b2 b b')"
      using Node.hyps(2) diff_b2 a1 Node.prems(3) by auto
    have diff_ab': "id_set (replace b2 b b') \<inter> id_set b1 = {}"
      using same_ids_replace diff_b2 a1 Node.prems(3) diff_ab by auto
    have diff_bc': "id_set (replace b2 b b') \<inter> id_set b3 = {}"
      using same_ids_replace diff_b2 a1 Node.prems(3) diff_bc by auto
    have diff_bd': "id_set (replace b2 b b') \<inter> id_set b4 = {}"
      using same_ids_replace diff_b2 a1 Node.prems(3) diff_bd by auto
    have ?case using replace_re diff_b1 diff_b2' diff_b3 diff_b4 diff_ab' diff_ac diff_ad diff_bc' diff_bd' diff_cd diff2 by (simp add: inf_commute) 
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(3) apply auto[1]
      using no_replace no_belong_b2 Node.prems(3) apply auto[1]
      using no_replace no_belong_b4 Node.prems(3) by auto
    have diff_b3': "diff_ids (replace b3 b b')"
      using Node.hyps(3) diff_b3 a2 Node.prems(3) by auto
    have diff_ac': "id_set (replace b3 b b') \<inter> id_set b1 = {}"
      using same_ids_replace diff_b3 a2 Node.prems(3) diff_ac by auto
    have diff_bc': "id_set (replace b3 b b') \<inter> id_set b2 = {}"
      using same_ids_replace diff_b3 a2 Node.prems(3) diff_bc by auto
    have diff_cd': "id_set (replace b3 b b') \<inter> id_set b4 = {}"
      using same_ids_replace diff_b3 a2 Node.prems(3) diff_cd by auto
    have ?case using replace_re diff_b1 diff_b2 diff_b3' diff_b4 diff_ab diff_ac' diff_ad diff_bc' diff_bd diff_cd' diff2 by (simp add: inf_commute) 
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(3) apply auto[1]
      using no_replace no_belong_b2 Node.prems(3) apply auto[1]
      using no_replace no_belong_b3 Node.prems(3) by auto
    have diff_b4': "diff_ids (replace b4 b b')"
      using Node.hyps(4) diff_b4 a3 Node.prems(3) by auto
    have diff_ad': "id_set (replace b4 b b') \<inter> id_set b1 = {}"
      using same_ids_replace diff_b4 a3 Node.prems(3) diff_ad by auto
    have diff_bd': "id_set (replace b4 b b') \<inter> id_set b2 = {}"
      using same_ids_replace diff_b4 a3 Node.prems(3) diff_bd by auto
    have diff_cd': "id_set (replace b4 b b') \<inter> id_set b3 = {}"
      using same_ids_replace diff_b4 a3 Node.prems(3) diff_cd by auto
    have ?case using replace_re diff_b1 diff_b2 diff_b3 diff_b4' diff_ab diff_ac diff_ad' diff_bc diff_bd' diff_cd' diff2 by (simp add: inf_commute)
  }
  ultimately have ?case using Node.prems(2) by fastforce
  then show ?case by auto
qed

lemma diff_ids_alloc_fail:
  "diff_ids_valid bset \<Longrightarrow>
  \<not> (exists_freelevel bset lv) \<Longrightarrow>
  diff_ids_valid (fst (alloc bset lv ids))"
  unfolding alloc_def Let_def by auto

lemma the_P:
  "\<exists>!x. P x \<Longrightarrow>
  y = (THE x. P x) \<Longrightarrow>
  P y"
  by (auto intro: theI)

lemma diff_ids_alloc_branch1:
  "diff_ids_valid bset \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax = lv \<Longrightarrow>
  (newbset, newids, re, reid) = alloc1 bset lv ids \<Longrightarrow>
  diff_ids_valid newbset"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "exists_freelevel bset lv"
     and a2: "lmax = freesets_maxlevel bset lv"
     and a3: "lmax = lv"
     and a4: "(newbset, newids, re, reid) = alloc1 bset lv ids"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a1 by auto
  have eq_lv: "lv = (THE lmax. lmax \<le> lv \<and>
                    freesets_level_pool bset lmax \<noteq> {} \<and>
                    (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a2 a3 unfolding freesets_maxlevel_def by auto
  have the_lv: "lv \<le> lv \<and>
               freesets_level_pool bset lv \<noteq> {} \<and>
               (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lv)"
    using the_P[OF exi_lmax eq_lv] by auto
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
    using the_lv unfolding freesets_level_pool_def by auto
  let ?blo = "SOME b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
  have diff_blo: "diff_ids ?blo"
    using diff_bset1 exi_b
    by (metis (mono_tags, lifting) some_eq_ex) 
  have exi_l: "\<exists>l. l \<in> freesets_level ?blo lv"
    using someI_ex[OF exi_b] by auto
  let ?l = "SOME l. l \<in> freesets_level ?blo lv"
  have leaf_belong: "L ?l \<in> set ?blo"
    using exi_l unfolding freesets_level_def freesets_def
    by (metis (no_types, lifting) CollectD someI_ex) 
  have exi_newb: "\<exists>newb. newb = replace ?blo ?l (set_state_type ?l ALLOC)"
    by simp
  let ?newb = "SOME newb. newb = replace ?blo ?l (set_state_type ?l ALLOC)"
  have diff_newblo: "diff_ids ?newb"
    using diff_ids_replace diff_blo leaf_belong by simp
  have alloc1_re: "(newbset, newids, re, reid) = (((bset - {?blo}) \<union> {?newb}), ids, True, {snd (L ?l)})"
    using a4 unfolding alloc1_def by (metis some_eq_trivial)
  have diff_newbset1: "\<forall>b \<in> newbset. diff_ids b"
    using alloc1_re diff_bset1 diff_blo diff_newblo by blast
  have same_ids_newblo: "id_set ?blo = id_set ?newb"
    using same_ids_replace diff_blo leaf_belong by simp
  have step1: "(\<forall>b1 b2. b1 \<in> (bset - {?blo}) \<and> b2 \<in> (bset - {?blo}) \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using diff_bset2 by auto
  have step2: "\<forall>b \<in> (bset - {?blo}). id_set b \<inter> id_set ?blo = {}"
    using diff_bset2
    by (metis (mono_tags, lifting) DiffE exi_b insertCI some_eq_ex) 
  have newstep1: "(\<forall>b1 b2. b1 \<in> (newbset - {?newb}) \<and> b2 \<in> (newbset - {?newb}) \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using step1 alloc1_re by auto
  have newstep2: "\<forall>b \<in> (newbset - {?newb}). id_set b \<inter> id_set ?newb = {}"
    using step2 alloc1_re same_ids_newblo by auto
  have diff_newbset2: "(\<forall>b1 b2. b1 \<in> newbset \<and> b2 \<in> newbset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using newstep1 newstep2 by auto
  show ?thesis using diff_newbset1 diff_newbset2 diff_ids_valid_def by auto
qed

lemma ids_overlap_empty:
  "id_set oth \<subseteq> ids \<Longrightarrow>
  snd (L x) \<in> ids \<Longrightarrow>
  id_set oth \<inter> {snd (L x)} = {} \<Longrightarrow>
  lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_set oth \<inter> id_set (fst (split x ids (lv - lmax))) = {}"
proof(induct "lv - lmax" arbitrary: oth x ids lmax)
  case 0
  then show ?case by linarith
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide x ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
    unfolding divide_def Let_def by auto
  have notbelong_ll: "snd ll \<notin> ids"
    using divide_notbelong Suc(7) pdivide by auto
  have ll_empty_oth: "id_set oth \<inter> {snd ll} = {}"
    using Suc(3) notbelong_ll by auto
  have notbelong_lr: "snd lr \<notin> ids"
    using divide_notbelong Suc(7) pdivide by auto
  have notbelong_rl: "snd rl \<notin> ids"
    using divide_notbelong Suc(7) pdivide by auto
  have notbelong_rr: "snd rr \<notin> ids"
    using divide_notbelong Suc(7) pdivide by auto
  have notbelong: "id_set oth \<inter> {snd ll, snd lr, snd rl, snd rr} = {}"
    using Suc(3) notbelong_ll notbelong_lr notbelong_rl notbelong_rr by auto
  let ?newids = "snd (divide x ids)"
  have step': "fst (split x ids (lv - lmax)) = Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
    using split_induct Suc(6) pdivide by (meson zero_less_diff)
  have belong_ll: "snd ll \<in> ?newids"
    using divide_belong pdivide by auto
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_lmax: "lv = Suc lmax"
      using Suc(2) xa_eq_1 by linarith
    have split_ll: "fst (split (Leaf ll) ?newids (lv - lmax - 1)) = Leaf ll"
      using lv_suc_lmax by auto
    have step1: "fst (split x ids (lv - lmax)) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      using step' split_ll by auto
    have co: "id_set (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) = {snd ll, snd lr, snd rl, snd rr}"
      unfolding id_set_def by auto
    have ?case using step1 co notbelong by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_lmax: "xa = lv - Suc lmax"
      using Suc(2) by linarith
    have suc_lmax_less_lv: "Suc lmax < lv"
      using Suc(3) xa_gr_1 xa_lv_suc_lmax by linarith
    have co1: "id_set (Node (fst (split (Leaf ll) ?newids (lv - Suc lmax))) (Leaf lr) (Leaf rl) (Leaf rr)) =
               id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<union> id_set (Leaf lr) \<union> id_set (Leaf rl) \<union> id_set (Leaf rr)"
      using id_set_node by auto
    have co2: "id_set (Leaf lr) \<union> id_set (Leaf rl) \<union> id_set (Leaf rr) = {snd lr, snd rl, snd rr}"
      unfolding id_set_def by auto
    have co: "id_set (Node (fst (split (Leaf ll) ?newids (lv - Suc lmax))) (Leaf lr) (Leaf rl) (Leaf rr)) =
              id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<union> {snd lr, snd rl, snd rr}"
      using co1 co2 by auto
    have ids_belong: "ids \<subseteq> snd (divide x ids)"
      unfolding divide_def Let_def using getnewid_inc by auto
    have oth_belong: "id_set oth \<subseteq> snd (divide x ids)"
      using Suc(3) ids_belong by auto
    have split_ll_empty_oth: "id_set oth \<inter> id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) = {}"
      using Suc(1) xa_lv_suc_lmax oth_belong belong_ll ll_empty_oth suc_lmax_less_lv divide_finite Suc(7) by auto
    have notbelong: "id_set oth \<inter> id_set (Node (fst (split (Leaf ll) ?newids (lv - Suc lmax))) (Leaf lr) (Leaf rl) (Leaf rr)) = {}"
      using split_ll_empty_oth notbelong co by auto
    have ?case using step' notbelong by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma diff_ids_split:
  "lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (L b) \<in> ids \<Longrightarrow>
  diff_ids (fst (split b ids (lv - lmax)))"
proof(induct "lv - lmax" arbitrary: lmax b ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
    unfolding divide_def Let_def by auto
  have diff_ab: "id_set (Leaf ll) \<inter> id_set (Leaf lr) = {}"
    unfolding id_set_def using divide_diff Suc(4) pdivide by auto
  have diff_ab': "{snd ll} \<inter> id_set (Leaf lr) = {}"
    using diff_ab unfolding id_set_def by auto
  have diff_ac: "id_set (Leaf ll) \<inter> id_set (Leaf rl) = {}"
    unfolding id_set_def using divide_diff Suc(4) pdivide by auto
  have diff_ac': "{snd ll} \<inter> id_set (Leaf rl) = {}"
    using diff_ac unfolding id_set_def by auto
  have diff_ad: "id_set (Leaf ll) \<inter> id_set (Leaf rr) = {}"
    unfolding id_set_def using divide_diff Suc(4) pdivide by auto
  have diff_ad': "{snd ll} \<inter> id_set (Leaf rr) = {}"
    using diff_ad unfolding id_set_def by auto
  have diff_bc: "id_set (Leaf lr) \<inter> id_set (Leaf rl) = {}"
    unfolding id_set_def using divide_diff2 Suc(4) pdivide by auto
  have diff_bd: "id_set (Leaf lr) \<inter> id_set (Leaf rr) = {}"
    unfolding id_set_def using divide_diff2 Suc(4) pdivide by auto
  have diff_cd: "id_set (Leaf rl) \<inter> id_set (Leaf rr) = {}"
    unfolding id_set_def using divide_diff2 Suc(4) pdivide by auto
  let ?newids = "snd (divide b ids)"
  have belong_ll: "snd ll \<in> ?newids"
    using divide_belong pdivide by auto
  have belong_lr: "id_set (Leaf lr) \<subseteq> ?newids"
    unfolding id_set_def using divide_belong pdivide by auto
  have belong_rl: "id_set (Leaf rl) \<subseteq> ?newids"
    unfolding id_set_def using divide_belong pdivide by auto
  have belong_rr: "id_set (Leaf rr) \<subseteq> ?newids"
    unfolding id_set_def using divide_belong pdivide by auto
  have step': "fst (split b ids (lv - lmax)) = Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using split_induct Suc(3) pdivide by (meson zero_less_diff)
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_lmax: "lv = Suc lmax"
      using Suc(2) xa_eq_1 by linarith
    have split_ll: "fst (split (Leaf ll) ?newids (lv - lmax - 1)) = Leaf ll"
      using lv_suc_lmax by auto
    have step1: "fst (split b ids (lv - lmax)) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      using step' split_ll by auto
    have diff_node: "diff_ids (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr))"
      using diff2 diff1
      using diff_ab diff_ac diff_ad diff_bc diff_bd diff_cd by auto
    have ?case using step1 diff_node by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_lmax: "xa = lv - Suc lmax"
      using Suc(2) by linarith
    have suc_lmax_less_lv: "Suc lmax < lv"
      using Suc(3) xa_gr_1 xa_lv_suc_lmax by linarith
    have split2: "diff_ids (fst (split (Leaf ll) ?newids (lv - Suc lmax)))"
      using Suc(1) xa_lv_suc_lmax suc_lmax_less_lv divide_finite Suc(4) belong_ll pdivide by auto
    have diff_ll_lr: "id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<inter> id_set (Leaf lr) = {}"
      using ids_overlap_empty belong_lr belong_ll diff_ab' suc_lmax_less_lv divide_finite Suc(4)
      by (metis inf_commute tree.sel(1)) 
    have diff_ll_rl: "id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<inter> id_set (Leaf rl) = {}"
      using ids_overlap_empty belong_rl belong_ll diff_ac' suc_lmax_less_lv divide_finite Suc(4)
      by (metis inf_commute tree.sel(1)) 
    have diff_ll_rr: "id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<inter> id_set (Leaf rr) = {}"
      using ids_overlap_empty belong_rr belong_ll diff_ad' suc_lmax_less_lv divide_finite Suc(4)
      by (metis inf_commute tree.sel(1))
    have diff_node: "diff_ids (Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr))"
      using diff2 diff1
      using split2 diff_ll_lr diff_ll_rl diff_ll_rr diff_bc diff_bd diff_cd by auto
    have ?case using step' diff_node by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma ids_split:
  "lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (L b) \<in> ids \<Longrightarrow>
  id_set (fst (split b ids (lv - lmax))) \<inter> ids = {}"
proof(induct "lv - lmax" arbitrary: lmax b ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
    unfolding divide_def Let_def by auto
  have notbelong_ll: "snd ll \<notin> ids"
    using divide_notbelong Suc(4) pdivide by auto
  have notbelong_lr: "snd lr \<notin> ids"
    using divide_notbelong Suc(4) pdivide by auto
  have notbelong_rl: "snd rl \<notin> ids"
    using divide_notbelong Suc(4) pdivide by auto
  have notbelong_rr: "snd rr \<notin> ids"
    using divide_notbelong Suc(4) pdivide by auto
  let ?newids = "snd (divide b ids)"
  have belong_ll: "snd ll \<in> ?newids"
    using divide_belong pdivide by auto
  have belong_ids: "ids \<subseteq> ?newids"
    unfolding divide_def Let_def using getnewid_inc by auto
  have step': "fst (split b ids (lv - lmax)) = Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
    using split_induct Suc(3) pdivide by (meson zero_less_diff)
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_lmax: "lv = Suc lmax"
      using Suc(2) xa_eq_1 by linarith
    have split_ll: "fst (split (Leaf ll) ?newids (lv - lmax - 1)) = Leaf ll"
      using lv_suc_lmax by auto
    have step1: "fst (split b ids (lv - lmax)) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      using step' split_ll by auto
    have ids_step1: "id_set (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) \<inter> ids = {}"
      using notbelong_ll notbelong_lr notbelong_rl notbelong_rr unfolding id_set_def by auto
    have ?case using step1 ids_step1 by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_lmax: "xa = lv - Suc lmax"
      using Suc(2) by linarith
    have suc_lmax_less_lv: "Suc lmax < lv"
      using Suc(3) xa_gr_1 xa_lv_suc_lmax by linarith
    have co1: "id_set (Node (fst (split (Leaf ll) ?newids (lv - Suc lmax))) (Leaf lr) (Leaf rl) (Leaf rr)) =
               id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<union> id_set (Leaf lr) \<union> id_set (Leaf rl) \<union> id_set (Leaf rr)"
      using id_set_node by auto
    have co2: "id_set (Leaf lr) \<union> id_set (Leaf rl) \<union> id_set (Leaf rr) = {snd lr, snd rl, snd rr}"
      unfolding id_set_def by auto
    have co: "id_set (Node (fst (split (Leaf ll) ?newids (lv - Suc lmax))) (Leaf lr) (Leaf rl) (Leaf rr)) =
              id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<union> {snd lr, snd rl, snd rr}"
      using co1 co2 by auto
    have split2': "id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<inter> ?newids = {}"
      using Suc(1) xa_lv_suc_lmax suc_lmax_less_lv divide_finite Suc(4) belong_ll pdivide by auto
    have split2: "id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<inter> ids = {}"
      using split2' belong_ids by auto
    have ids_step2: "(id_set (fst (split (Leaf ll) ?newids (lv - Suc lmax))) \<union> {snd lr, snd rl, snd rr}) \<inter> ids = {}"
      using split2 notbelong_lr notbelong_rl notbelong_rr by auto
    have ?case using step' co ids_step2 by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma ids_replace_leaf:
  "diff_ids blo \<Longrightarrow>
  id_set blo \<subseteq> ids \<Longrightarrow>
  L b \<in> tree.set blo \<Longrightarrow>
  id_set subbtr \<inter> ids = {} \<Longrightarrow>
  id_set (replace_leaf blo b subbtr) = id_set blo - {snd (L b)} \<union> id_set subbtr"
proof(induct blo)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(3) by fastforce
  have replace_leaf_step: "replace_leaf (Leaf x) b subbtr = subbtr"
    using leaf_b replace_leaf.simps(1) by auto
  show ?case using replace_leaf_step leaf_b unfolding id_set_def by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b2: "{snd (L b)} \<inter> id_set b2 = {}"
      using no_belong_b2 unfolding id_set_def
      using a0 diff_ab id_set_def tree.set_map by fastforce 
    have b_empty_b3: "{snd (L b)} \<inter> id_set b3 = {}"
      using no_belong_b3 unfolding id_set_def
      using a0 diff_ac id_set_def tree.set_map by fastforce 
    have b_empty_b4: "{snd (L b)} \<inter> id_set b4 = {}"
      using no_belong_b4 unfolding id_set_def
      using a0 diff_ad id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node (replace_leaf b1 b subbtr) b2 b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b2 no_belong_b3 no_belong_b4 by auto
    have step: "id_set (replace_leaf b1 b subbtr) = id_set b1 - {snd (L b)} \<union> id_set subbtr"
      using Node.hyps(1) diff_b1 Node.prems(2) a0 Node.prems(4) unfolding id_set_def by auto
    have step_node': "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                     id_set b1 - {snd (L b)} \<union> id_set subbtr \<union> id_set b2 \<union> id_set b3 \<union> id_set b4"
      using replace_leaf_step id_set_node step by auto
    have step_node'': "id_set b1 - {snd (L b)} \<union> id_set subbtr \<union> id_set b2 \<union> id_set b3 \<union> id_set b4 =
                      id_set b1 \<union> id_set b2 \<union> id_set b3 \<union> id_set b4 - {snd (L b)} \<union> id_set subbtr"
      using b_empty_b2 b_empty_b3 b_empty_b4 by auto
    have step_node: "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                    id_set (Node b1 b2 b3 b4) - {snd (L b)} \<union> id_set subbtr"
      using step_node' step_node'' id_set_node by auto
    have ?case using replace_leaf_step step_node by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b1: "{snd (L b)} \<inter> id_set b1 = {}"
      using no_belong_b1 unfolding id_set_def
      using a1 diff_ab id_set_def tree.set_map by fastforce 
    have b_empty_b3: "{snd (L b)} \<inter> id_set b3 = {}"
      using no_belong_b3 unfolding id_set_def
      using a1 diff_bc id_set_def tree.set_map by fastforce 
    have b_empty_b4: "{snd (L b)} \<inter> id_set b4 = {}"
      using no_belong_b4 unfolding id_set_def
      using a1 diff_bd id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node b1 (replace_leaf b2 b subbtr) b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b3 no_belong_b4 by auto
    have step: "id_set (replace_leaf b2 b subbtr) = id_set b2 - {snd (L b)} \<union> id_set subbtr"
      using Node.hyps(2) diff_b2 Node.prems(2) a1 Node.prems(4) unfolding id_set_def by auto
    have step_node': "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                     id_set b1 \<union> id_set b2 - {snd (L b)} \<union> id_set subbtr \<union> id_set b3 \<union> id_set b4"
      using replace_leaf_step id_set_node step
      using b_empty_b1 by auto 
    have step_node'': "id_set b1 \<union> id_set b2 - {snd (L b)} \<union> id_set subbtr \<union> id_set b3 \<union> id_set b4 =
                      id_set b1 \<union> id_set b2 \<union> id_set b3 \<union> id_set b4 - {snd (L b)} \<union> id_set subbtr"
      using b_empty_b3 b_empty_b4 by auto
    have step_node: "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                    id_set (Node b1 b2 b3 b4) - {snd (L b)} \<union> id_set subbtr"
      using step_node' step_node'' id_set_node by auto
    have ?case using replace_leaf_step step_node by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b1: "{snd (L b)} \<inter> id_set b1 = {}"
      using no_belong_b1 unfolding id_set_def
      using a2 diff_ac id_set_def tree.set_map by fastforce 
    have b_empty_b2: "{snd (L b)} \<inter> id_set b2 = {}"
      using no_belong_b2 unfolding id_set_def
      using a2 diff_bc id_set_def tree.set_map by fastforce 
    have b_empty_b4: "{snd (L b)} \<inter> id_set b4 = {}"
      using no_belong_b4 unfolding id_set_def
      using a2 diff_cd id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node b1 b2 (replace_leaf b3 b subbtr) b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b4 by auto
    have step: "id_set (replace_leaf b3 b subbtr) = id_set b3 - {snd (L b)} \<union> id_set subbtr"
      using Node.hyps(3) diff_b3 Node.prems(2) a2 Node.prems(4) unfolding id_set_def by auto
    have step_node': "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                     id_set b1 \<union> id_set b2 \<union> id_set b3 - {snd (L b)} \<union> id_set subbtr \<union> id_set b4"
      using replace_leaf_step id_set_node step
      using b_empty_b1 b_empty_b2 by auto
    have step_node'': "id_set b1 \<union> id_set b2 \<union> id_set b3 - {snd (L b)} \<union> id_set subbtr \<union> id_set b4 =
                      id_set b1 \<union> id_set b2 \<union> id_set b3 \<union> id_set b4 - {snd (L b)} \<union> id_set subbtr"
      using b_empty_b4 by auto
    have step_node: "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                    id_set (Node b1 b2 b3 b4) - {snd (L b)} \<union> id_set subbtr"
      using step_node' step_node'' id_set_node by auto
    have ?case using replace_leaf_step step_node by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b1: "{snd (L b)} \<inter> id_set b1 = {}"
      using no_belong_b1 unfolding id_set_def
      using a3 diff_ad id_set_def tree.set_map by fastforce 
    have b_empty_b2: "{snd (L b)} \<inter> id_set b2 = {}"
      using no_belong_b2 unfolding id_set_def
      using a3 diff_bd id_set_def tree.set_map by fastforce 
    have b_empty_b3: "{snd (L b)} \<inter> id_set b3 = {}"
      using no_belong_b3 unfolding id_set_def
      using a3 diff_cd id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node b1 b2 b3 (replace_leaf b4 b subbtr)"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b3 by auto
    have step: "id_set (replace_leaf b4 b subbtr) = id_set b4 - {snd (L b)} \<union> id_set subbtr"
      using Node.hyps(4) diff_b4 Node.prems(2) a3 Node.prems(4) unfolding id_set_def by auto
    have step_node': "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                     id_set b1 \<union> id_set b2 \<union> id_set b3 \<union> id_set b4 - {snd (L b)} \<union> id_set subbtr"
      using replace_leaf_step id_set_node step
      using b_empty_b1 b_empty_b2 b_empty_b3 by auto
    have step_node: "id_set (replace_leaf (Node b1 b2 b3 b4) b subbtr) =
                    id_set (Node b1 b2 b3 b4) - {snd (L b)} \<union> id_set subbtr"
      using step_node' id_set_node by auto
    have ?case using replace_leaf_step step_node by auto
  }
  ultimately have ?case
    using Node.prems(3) by auto 
  then show ?case by auto
qed

lemma diff_ids_replace_leaf:
  "diff_ids blo \<Longrightarrow>
  lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_set blo \<subseteq> ids \<Longrightarrow>
  L b \<in> tree.set blo \<Longrightarrow>
  diff_ids (replace_leaf blo b (fst (split b ids (lv - lmax))))"
proof(induct blo)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(5) by fastforce
  have b_belong: "snd (L b) \<in> ids"
    using Leaf.prems(4) leaf_b unfolding id_set_def by auto
  have diff_b_split: "diff_ids (fst (split b ids (lv - lmax)))"
    using diff_ids_split Leaf.prems(2,3) b_belong by auto
  have replace_leaf_step: "replace_leaf (Leaf x) b (fst (split b ids (lv - lmax))) = fst (split b ids (lv - lmax))"
    using leaf_b replace_leaf.simps(1) by auto
  show ?case using replace_leaf_step diff_b_split by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have b_belong: "snd (L b) \<in> ids"
    using Node.prems(4,5) unfolding id_set_def
    by (metis contra_subsetD image_eqI tree.set_map) 
  have ids_subbtr: "id_set (fst (split b ids (lv - lmax))) \<inter> ids = {}"
      using ids_split Node.prems(2,3) b_belong by auto
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node (replace_leaf b1 b (fst (split b ids (lv - lmax)))) b2 b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b2 no_belong_b3 no_belong_b4 by auto
    have diff_b1': "diff_ids (replace_leaf b1 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(1) diff_b1 Node.prems(2,3,4) a0 unfolding id_set_def by fastforce
    have ids_replace_leaf: "id_set (replace_leaf b1 b (fst (split b ids (lv - lmax)))) = id_set b1 - {snd (L b)} \<union> id_set (fst (split b ids (lv - lmax)))"
      using ids_replace_leaf diff_b1 Node.prems(4) a0 ids_subbtr unfolding id_set_def by fastforce
    have diff_ab': "id_set (replace_leaf b1 b (fst (split b ids (lv - lmax)))) \<inter> id_set b2 = {}"
      using Node.prems(4) diff_ab ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_ac': "id_set (replace_leaf b1 b (fst (split b ids (lv - lmax)))) \<inter> id_set b3 = {}"
      using Node.prems(4) diff_ac ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_ad': "id_set (replace_leaf b1 b (fst (split b ids (lv - lmax)))) \<inter> id_set b4 = {}"
      using Node.prems(4) diff_ad ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_replace_leaf_step: "diff_ids (Node (replace_leaf b1 b (fst (split b ids (lv - lmax)))) b2 b3 b4)"
      using diff1 diff2 diff_b1' diff_b2 diff_b3 diff_b4
      using diff_ab' diff_ac' diff_ad' diff_bc diff_bd diff_cd by auto
    have ?case using replace_leaf_step diff_replace_leaf_step by auto
  }
  moreover 
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node b1 (replace_leaf b2 b (fst (split b ids (lv - lmax)))) b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b3 no_belong_b4 by auto
    have diff_b2': "diff_ids (replace_leaf b2 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(2) diff_b2 Node.prems(2,3,4) a1 unfolding id_set_def by fastforce
    have ids_replace_leaf: "id_set (replace_leaf b2 b (fst (split b ids (lv - lmax)))) = id_set b2 - {snd (L b)} \<union> id_set (fst (split b ids (lv - lmax)))"
      using ids_replace_leaf diff_b2 Node.prems(4) a1 ids_subbtr unfolding id_set_def by fastforce
    have diff_ab': "id_set (replace_leaf b2 b (fst (split b ids (lv - lmax)))) \<inter> id_set b1 = {}"
      using Node.prems(4) diff_ab ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_bc': "id_set (replace_leaf b2 b (fst (split b ids (lv - lmax)))) \<inter> id_set b3 = {}"
      using Node.prems(4) diff_bc ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_bd': "id_set (replace_leaf b2 b (fst (split b ids (lv - lmax)))) \<inter> id_set b4 = {}"
      using Node.prems(4) diff_bd ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_replace_leaf_step: "diff_ids (Node b1 (replace_leaf b2 b (fst (split b ids (lv - lmax)))) b3 b4)"
      using diff1 diff2 diff_b1 diff_b2' diff_b3 diff_b4
      using diff_ab' diff_ac diff_ad diff_bc' diff_bd' diff_cd
      by (simp add: inf_sup_aci(1))
    have ?case using replace_leaf_step diff_replace_leaf_step by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node b1 b2 (replace_leaf b3 b (fst (split b ids (lv - lmax)))) b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b4 by auto
    have diff_b3': "diff_ids (replace_leaf b3 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(3) diff_b3 Node.prems(2,3,4) a2 unfolding id_set_def by fastforce
    have ids_replace_leaf: "id_set (replace_leaf b3 b (fst (split b ids (lv - lmax)))) = id_set b3 - {snd (L b)} \<union> id_set (fst (split b ids (lv - lmax)))"
      using ids_replace_leaf diff_b3 Node.prems(4) a2 ids_subbtr unfolding id_set_def by fastforce
    have diff_ac': "id_set (replace_leaf b3 b (fst (split b ids (lv - lmax)))) \<inter> id_set b1 = {}"
      using Node.prems(4) diff_ac ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_bc': "id_set (replace_leaf b3 b (fst (split b ids (lv - lmax)))) \<inter> id_set b2 = {}"
      using Node.prems(4) diff_bc ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_cd': "id_set (replace_leaf b3 b (fst (split b ids (lv - lmax)))) \<inter> id_set b4 = {}"
      using Node.prems(4) diff_cd ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_replace_leaf_step: "diff_ids (Node b1 b2 (replace_leaf b3 b (fst (split b ids (lv - lmax)))) b4)"
      using diff1 diff2 diff_b1 diff_b2 diff_b3' diff_b4
      using diff_ab diff_ac' diff_ad diff_bc' diff_bd diff_cd'
      by (simp add: inf_sup_aci(1))
    have ?case using replace_leaf_step diff_replace_leaf_step by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node b1 b2 b3 (replace_leaf b4 b (fst (split b ids (lv - lmax))))"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b3 by auto
    have diff_b4': "diff_ids (replace_leaf b4 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(4) diff_b4 Node.prems(2,3,4) a3 unfolding id_set_def by fastforce
    have ids_replace_leaf: "id_set (replace_leaf b4 b (fst (split b ids (lv - lmax)))) = id_set b4 - {snd (L b)} \<union> id_set (fst (split b ids (lv - lmax)))"
      using ids_replace_leaf diff_b4 Node.prems(4) a3 ids_subbtr unfolding id_set_def by fastforce
    have diff_ad': "id_set (replace_leaf b4 b (fst (split b ids (lv - lmax)))) \<inter> id_set b1 = {}"
      using Node.prems(4) diff_ad ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_bd': "id_set (replace_leaf b4 b (fst (split b ids (lv - lmax)))) \<inter> id_set b2 = {}"
      using Node.prems(4) diff_bd ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_cd': "id_set (replace_leaf b4 b (fst (split b ids (lv - lmax)))) \<inter> id_set b3 = {}"
      using Node.prems(4) diff_cd ids_subbtr ids_replace_leaf unfolding id_set_def
      using insert_disjoint(2) by auto
    have diff_replace_leaf_step: "diff_ids (Node b1 b2 b3 (replace_leaf b4 b (fst (split b ids (lv - lmax)))))"
      using diff1 diff2 diff_b1 diff_b2 diff_b3 diff_b4'
      using diff_ab diff_ac diff_ad' diff_bc diff_bd' diff_cd'
      by (simp add: inf_sup_aci(1))
    have ?case using replace_leaf_step diff_replace_leaf_step by auto
  }
  ultimately have ?case
    using Node.prems(5) by fastforce 
  then show ?case by auto
qed

lemma diff_ids_alloc_branch2:
  "diff_ids_valid bset \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<forall>b\<in>bset. id_set b \<subseteq> ids \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax \<noteq> lv \<Longrightarrow>
  blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {}) \<Longrightarrow>
  b = (SOME l. l \<in> freesets_level blo lmax) \<Longrightarrow>
  (subbtr, ids') = split b ids (lv - lmax) \<Longrightarrow>
  newbtr = replace_leaf blo b subbtr \<Longrightarrow>
  newbset = bset - {blo} \<union> {newbtr} \<Longrightarrow>
  diff_ids_valid newbset"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "finite ids"
     and a2: "\<forall>b\<in>bset. id_set b \<subseteq> ids"
     and a3: "exists_freelevel bset lv"
     and a4: "lmax = freesets_maxlevel bset lv"
     and a5: "lmax \<noteq> lv"
     and a6: "blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {})"
     and a7: "b = (SOME l. l \<in> freesets_level blo lmax)"
     and a8: "(subbtr, ids') = split b ids (lv - lmax)"
     and a9: "newbtr = replace_leaf blo b subbtr"
     and a10: "newbset = bset - {blo} \<union> {newbtr}"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a3 by auto
  have eq_lmax: "lmax = (THE lmax. lmax \<le> lv \<and>
                        freesets_level_pool bset lmax \<noteq> {} \<and>
                        (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a4 unfolding freesets_maxlevel_def by auto
  have the_lmax: "lmax < lv \<and>
                 freesets_level_pool bset lmax \<noteq> {} \<and>
                 (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using the_P[OF exi_lmax eq_lmax] a5 by auto
  have lmax_le_lv: "lmax < lv" using the_lmax by auto
(*------------------------------------------------------------------------------------------------*)
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lmax \<noteq> {}"
    using the_lmax unfolding freesets_level_pool_def by auto
  have exi_blo: "blo \<in> bset \<and> freesets_level blo lmax \<noteq> {}"
    using someI_ex[OF exi_b] a6 by auto
  have diff_blo: "diff_ids blo"
    using diff_bset1 exi_blo by auto
  have ids_blo: "id_set blo \<subseteq> ids"
    using a2 exi_blo by auto
  have exi_l: "\<exists>l. l \<in> freesets_level blo lmax"
    using exi_blo by auto
  have exi_b: "b \<in> freesets_level blo lmax"
    using someI_ex[OF exi_l] a7 by auto
  have b_belong_blo: "L b \<in> tree.set blo"
    using exi_b unfolding freesets_level_def freesets_def by auto
  have ids_b: "snd (L b) \<in> ids"
    using exi_b unfolding freesets_level_def freesets_def
    using ids_blo unfolding id_set_def using tree.set_map by fastforce
(*------------------------------------------------------------------------------------------------*)
  have ids_subbtr: "id_set subbtr \<inter> ids = {}"
    using ids_split lmax_le_lv a1 ids_b a8 fst_conv by metis
  have ids_newbtr: "id_set newbtr = id_set blo - {snd (L b)} \<union> id_set subbtr"
    using ids_replace_leaf diff_blo ids_blo b_belong_blo ids_subbtr a9 by auto
  have diff_newbtr: "diff_ids newbtr"
    using diff_ids_replace_leaf diff_blo lmax_le_lv a1 ids_blo b_belong_blo a8 a9 fst_conv by metis
  have diff_newbset1: "\<forall>b \<in> newbset. diff_ids b"
    using a10 diff_bset1 diff_blo diff_newbtr by blast
  have step1: "(\<forall>b1 b2. b1 \<in> (bset - {blo}) \<and> b2 \<in> (bset - {blo}) \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using diff_bset2 by auto
  have step2: "\<forall>b \<in> (bset - {blo}). id_set b \<inter> id_set blo = {}"
    using diff_bset2 by (metis (mono_tags, lifting) DiffE exi_blo insertCI) 
  have newstep1: "(\<forall>b1 b2. b1 \<in> (newbset - {newbtr}) \<and> b2 \<in> (newbset - {newbtr}) \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using step1 a10 by auto
  have newstep2: "\<forall>b \<in> (newbset - {newbtr}). id_set b \<inter> id_set newbtr = {}"
    using step2 ids_newbtr ids_subbtr a2 a10 disjoint_iff_not_equal by blast
  have diff_newbset2: "(\<forall>b1 b2. b1 \<in> newbset \<and> b2 \<in> newbset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using newstep1 newstep2 by auto
  have diff_newbset: "diff_ids_valid newbset"
    using diff_newbset1 diff_newbset2 diff_ids_valid_def by auto
  then show ?thesis by auto
qed

lemma diff_ids_free_branch1:
  "diff_ids_valid bset \<Longrightarrow>
  \<not> (\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)) \<Longrightarrow>
  diff_ids_valid (fst (free bset b lv ids))"
  unfolding free_def Let_def by auto

lemma diff_ids_free_branch2:
  "diff_ids_valid bset \<Longrightarrow>
  \<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b) \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  diff_ids_valid (fst (free bset b lv ids))"
  unfolding free_def Let_def by auto

lemma combine_id:
  "id_set b \<subseteq> ids \<Longrightarrow>
  id_set (fst (combine b ids)) \<subseteq> snd (combine b ids)"
  unfolding id_set_def combine_def Let_def
  apply auto
  using newid_in_getnewid2 by auto

lemma combine_anot:
  "finite ids \<Longrightarrow>
  b = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)) \<Longrightarrow>
  id_set (fst (combine b ids)) \<inter> ids = {}"
  unfolding id_set_def combine_def Let_def
  apply auto
  using getnewid2_anot by auto

lemma ids_merge:
  "id_set B \<subseteq> ids \<Longrightarrow>
  ids \<subseteq> snd (merge B ids)"
proof(induct B arbitrary: ids)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have ids_b1: "id_set b1 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  have ids_b2: "id_set b2 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  have ids_b3: "id_set b3 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  have ids_b4: "id_set b4 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    have ids_com: "ids \<subseteq> snd (combine (Node b1 b2 b3 b4) ids)"
      using combine_ids by blast
    then have ?case using step by auto
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have ids_belong_m1: "ids \<subseteq> snd ?m1"
      using Node.hyps(1) ids_b1 by auto
    have b2_belong_m1: "id_set b2 \<subseteq> snd ?m1"
      using ids_b2 ids_belong_m1 by auto
    let ?m2 = "merge b2 (snd ?m1)"
    have m1_belong_m2: "snd ?m1 \<subseteq> snd ?m2"
      using Node.hyps(2) b2_belong_m1 by auto
    have b3_belong_m2: "id_set b3 \<subseteq> snd ?m2"
      using ids_b3 ids_belong_m1 m1_belong_m2 by auto
    let ?m3 = "merge b3 (snd ?m2)"
    have m2_belong_m3: "snd ?m2 \<subseteq> snd ?m3"
      using Node.hyps(3) b3_belong_m2 by auto
    have b4_belong_m3: "id_set b4 \<subseteq> snd ?m3"
      using ids_b4 ids_belong_m1 m1_belong_m2 m2_belong_m3 by auto
    let ?m4 = "merge b4 (snd ?m3)"
    have m3_belong_m4: "snd ?m3 \<subseteq> snd ?m4"
      using Node.hyps(4) b4_belong_m3 by auto
    have ids_belong_m4: "ids \<subseteq> snd ?m4"
      using ids_belong_m1 m1_belong_m2 m2_belong_m3 m3_belong_m4 by auto
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson 
    have m4_belong_com: "snd ?m4 \<subseteq> snd (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4))"
      using combine_ids by blast
    have ?case using step ids_belong_m4 m4_belong_com by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma ids_merge2:
  "id_set B \<subseteq> ids \<Longrightarrow>
  id_set (fst (merge B ids)) \<subseteq> snd (merge B ids)"
proof(induct B arbitrary: ids)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have ids_b1: "id_set b1 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  have ids_b2: "id_set b2 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  have ids_b3: "id_set b3 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  have ids_b4: "id_set b4 \<subseteq> ids"
    using Node.prems(1) by (simp add: id_set_node) 
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    have ids_com: "id_set (fst (combine (Node b1 b2 b3 b4) ids)) \<subseteq> snd (combine (Node b1 b2 b3 b4) ids)"
      using combine_id Node.prems(1) by auto
    then have ?case using step by auto
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have induct1: "id_set (fst ?m1) \<subseteq> snd ?m1"
      using Node.hyps(1) ids_b1 by auto
    have ids_belong_m1: "ids \<subseteq> snd ?m1"
      using ids_merge ids_b1 by auto
    have b2_belong_m1: "id_set b2 \<subseteq> snd ?m1"
      using ids_b2 ids_belong_m1 by auto

    let ?m2 = "merge b2 (snd ?m1)"
    have induct2: "id_set (fst ?m2) \<subseteq> snd ?m2"
      using Node.hyps(2) b2_belong_m1 by auto
    have m1_belong_m2: "snd ?m1 \<subseteq> snd ?m2"
      using ids_merge b2_belong_m1 by auto
    have b3_belong_m2: "id_set b3 \<subseteq> snd ?m2"
      using ids_b3 ids_belong_m1 m1_belong_m2 by auto

    let ?m3 = "merge b3 (snd ?m2)"
    have induct3: "id_set (fst ?m3) \<subseteq> snd ?m3"
      using Node.hyps(3) b3_belong_m2 by auto
    have m2_belong_m3: "snd ?m2 \<subseteq> snd ?m3"
      using ids_merge b3_belong_m2 by auto
    have b4_belong_m3: "id_set b4 \<subseteq> snd ?m3"
      using ids_b4 ids_belong_m1 m1_belong_m2 m2_belong_m3 by auto

    let ?m4 = "merge b4 (snd ?m3)"
    have induct4: "id_set (fst ?m4) \<subseteq> snd ?m4"
      using Node.hyps(4) b4_belong_m3 by auto
    have m3_belong_m4: "snd ?m3 \<subseteq> snd ?m4"
      using ids_merge b4_belong_m3 by auto

    have induct5: "id_set (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) \<subseteq> snd ?m4"
      using induct1 induct2 induct3 induct4 m1_belong_m2 m2_belong_m3 m3_belong_m4 id_set_node by blast
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson 
    have ids_com: "id_set (fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4))) \<subseteq> snd (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4))"
      using combine_id induct5 by auto
    have ?case using step ids_com by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma finite_merge:
  "finite ids \<Longrightarrow>
  finite (snd (merge B ids))"
proof(induct B arbitrary: ids)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    have ?case using combine_finite Node.prems(1) step by auto
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have finite_m1: "finite (snd ?m1)"
      using Node.hyps(1) Node.prems(1) by auto
    let ?m2 = "merge b2 (snd ?m1)"
    have finite_m2: "finite (snd ?m2)"
      using Node.hyps(2) finite_m1 by auto
    let ?m3 = "merge b3 (snd ?m2)"
    have finite_m3: "finite (snd ?m3)"
      using Node.hyps(3) finite_m2 by auto
    let ?m4 = "merge b4 (snd ?m3)"
    have finite_m4: "finite (snd ?m4)"
      using Node.hyps(4) finite_m3 by auto
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson
    have ?case using combine_finite finite_m4 step by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma overlap_merge:
  "finite ids \<Longrightarrow>
  id_set oth \<subseteq> ids \<Longrightarrow>
  id_set B \<subseteq> ids \<Longrightarrow>
  id_set oth \<inter> id_set B = {} \<Longrightarrow>
  id_set oth \<inter> id_set (fst (merge B ids)) = {}"
proof(induct B arbitrary: ids)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have ids_b1: "id_set b1 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have ids_b2: "id_set b2 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have ids_b3: "id_set b3 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have ids_b4: "id_set b4 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have oth_b1: "id_set oth \<inter> id_set b1 = {}"
    using Node.prems(4) id_set_node by auto 
  have oth_b2: "id_set oth \<inter> id_set b2 = {}"
    using Node.prems(4) id_set_node by auto 
  have oth_b3: "id_set oth \<inter> id_set b3 = {}"
    using Node.prems(4) id_set_node by auto 
  have oth_b4: "id_set oth \<inter> id_set b4 = {}"
    using Node.prems(4) id_set_node by auto 
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    have com_ids_empty: "id_set (fst (combine (Node b1 b2 b3 b4) ids)) \<inter> ids = {}"
      using combine_anot Node.prems(1) a0 by blast
    have ?case using step com_ids_empty Node.prems(2) by auto
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have over_m1: "id_set oth \<inter> id_set (fst ?m1) = {}"
      using Node.hyps(1) Node.prems(1,2) ids_b1 oth_b1 by auto
    have finite_m1: "finite (snd ?m1)"
      using finite_merge Node.prems(1) by auto
    have ids_belong_m1: "ids \<subseteq> snd ?m1"
      using ids_merge ids_b1 by auto
    have oth_belong_m1: "id_set oth \<subseteq> snd ?m1"
      using Node.prems(2) ids_belong_m1 by auto
    have b2_belong_m1: "id_set b2 \<subseteq> snd ?m1"
      using ids_b2 ids_belong_m1 by auto

    let ?m2 = "merge b2 (snd ?m1)"
    have over_m2: "id_set oth \<inter> id_set (fst ?m2) = {}"
      using Node.hyps(2) finite_m1 oth_belong_m1 b2_belong_m1 oth_b2 by auto
    have finite_m2: "finite (snd ?m2)"
      using finite_merge finite_m1 by auto
    have m1_belong_m2: "snd ?m1 \<subseteq> snd ?m2"
      using ids_merge b2_belong_m1 by auto
    have oth_belong_m2: "id_set oth \<subseteq> snd ?m2"
      using oth_belong_m1 m1_belong_m2 by auto
    have b3_belong_m2: "id_set b3 \<subseteq> snd ?m2"
      using ids_b3 ids_belong_m1 m1_belong_m2 by auto

    let ?m3 = "merge b3 (snd ?m2)"
    have over_m3: "id_set oth \<inter> id_set (fst ?m3) = {}"
      using Node.hyps(3) finite_m2 oth_belong_m2 b3_belong_m2 oth_b3 by auto
    have finite_m3: "finite (snd ?m3)"
      using finite_merge finite_m2 by auto
    have m2_belong_m3: "snd ?m2 \<subseteq> snd ?m3"
      using ids_merge b3_belong_m2 by auto
    have oth_belong_m3: "id_set oth \<subseteq> snd ?m3"
      using oth_belong_m1 m1_belong_m2 m2_belong_m3 by auto
    have b4_belong_m3: "id_set b4 \<subseteq> snd ?m3"
      using ids_b4 ids_belong_m1 m1_belong_m2 m2_belong_m3 by auto

    let ?m4 = "merge b4 (snd ?m3)"
    have over_m4: "id_set oth \<inter> id_set (fst ?m4) = {}"
      using Node.hyps(4) finite_m3 oth_belong_m3 b4_belong_m3 oth_b4 by auto
    have finite_m4: "finite (snd ?m4)"
      using finite_merge finite_m3 by auto
    have m3_belong_m4: "snd ?m3 \<subseteq> snd ?m4"
      using ids_merge b4_belong_m3 by auto
    have oth_belong_m4: "id_set oth \<subseteq> snd ?m4"
      using oth_belong_m1 m1_belong_m2 m2_belong_m3 m3_belong_m4 by auto

    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson 
    have oth_com: "id_set oth \<inter> id_set (fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4))) = {}"
    proof(cases "\<exists>xa xb xc xd. Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))")
      case True
      have com_m4: "id_set (fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4))) \<inter> (snd ?m4) = {}"
        using combine_anot finite_m4 True by blast
      show ?thesis using oth_belong_m4 com_m4 by auto
    next
      case False
      have step': "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)"
        unfolding combine_def using False by auto
      have oth_node: "id_set oth \<inter> id_set (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) = {}"
        using over_m1 over_m2 over_m3 over_m4 unfolding id_set_def by auto
      show ?thesis using step' oth_node by auto
    qed
    have ?case using step oth_com by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma diff_ids_merge:
  "diff_ids B \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_set B \<subseteq> ids \<Longrightarrow>
  diff_ids (fst (merge B ids))"
proof(induct B arbitrary: ids)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have ids_b1: "id_set b1 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have ids_b2: "id_set b2 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have ids_b3: "id_set b3 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  have ids_b4: "id_set b4 \<subseteq> ids"
    using Node.prems(3) by (simp add: id_set_node) 
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    obtain newid where com: "fst (combine (Node b1 b2 b3 b4) ids) = Leaf (FREE, newid)"
      unfolding combine_def Let_def using fst_conv a0 by auto
    then have ?case using step diff1 by auto
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have diff_m1: "diff_ids (fst ?m1)"
      using Node.hyps(1) diff_b1 Node.prems(2) ids_b1 by auto
    have finite_m1: "finite (snd ?m1)"
      using finite_merge Node.prems(2) by auto
    have ids_m1: "id_set (fst ?m1) \<subseteq> snd ?m1"
      using ids_merge2 ids_b1 by auto
    have ids_belong_m1: "ids \<subseteq> snd ?m1"
      using ids_merge diff_b1 ids_b1 by auto
    have b2_belong_m1: "id_set b2 \<subseteq> snd ?m1"
      using ids_b2 ids_belong_m1 by auto
    have b3_belong_m1: "id_set b3 \<subseteq> snd ?m1"
      using ids_b3 ids_belong_m1 by auto
    have b4_belong_m1: "id_set b4 \<subseteq> snd ?m1"
      using ids_b4 ids_belong_m1 by auto
    have b2_m1: "id_set b2 \<inter> id_set (fst ?m1) = {}"
      using overlap_merge Node.prems(2) ids_b2 ids_b1 diff_ab
      by (simp add: Int_commute)
    have b3_m1: "id_set b3 \<inter> id_set (fst ?m1) = {}"
      using overlap_merge Node.prems(2) ids_b3 ids_b1 diff_ac
      by (simp add: Int_commute)
    have b4_m1: "id_set b4 \<inter> id_set (fst ?m1) = {}"
      using overlap_merge Node.prems(2) ids_b4 ids_b1 diff_ad
      by (simp add: Int_commute)

    let ?m2 = "merge b2 (snd ?m1)"
    have diff_m2: "diff_ids (fst ?m2)"
      using Node.hyps(2) diff_b2 finite_m1 b2_belong_m1 by auto
    have finite_m2: "finite (snd ?m2)"
      using finite_merge finite_m1 by auto
    have ids_m2: "id_set (fst ?m2) \<subseteq> snd ?m2"
      using ids_merge2 b2_belong_m1 by auto
    have m1_belong_m2: "snd ?m1 \<subseteq> snd ?m2"
      using ids_merge diff_b2 b2_belong_m1 by auto
    have b3_belong_m2: "id_set b3 \<subseteq> snd ?m2"
      using ids_b3 ids_belong_m1 m1_belong_m2 by auto
    have b4_belong_m2: "id_set b4 \<subseteq> snd ?m2"
      using ids_b4 ids_belong_m1 m1_belong_m2 by auto
    have m1_m2: "id_set (fst ?m1) \<inter> id_set (fst ?m2) = {}"
      using overlap_merge finite_m1 ids_m1 b2_belong_m1 b2_m1
      by (simp add: Int_commute)
    have b3_m2: "id_set b3 \<inter> id_set (fst ?m2) = {}"
      using overlap_merge finite_m1 b3_belong_m1 b2_belong_m1 diff_bc 
      by (simp add: Int_commute)
    have b4_m2: "id_set b4 \<inter> id_set (fst ?m2) = {}"
      using overlap_merge finite_m1 b4_belong_m1 b2_belong_m1 diff_bd 
      by (simp add: Int_commute)

    let ?m3 = "merge b3 (snd ?m2)"
    have diff_m3: "diff_ids (fst ?m3)"
      using Node.hyps(3) diff_b3 finite_m2 b3_belong_m2 by auto
    have finite_m3: "finite (snd ?m3)"
      using finite_merge finite_m2 by auto
    have ids_m3: "id_set (fst ?m3) \<subseteq> snd ?m3"
      using ids_merge2 b3_belong_m2 by auto
    have m2_belong_m3: "snd ?m2 \<subseteq> snd ?m3"
      using ids_merge diff_b3 b3_belong_m2 by auto
    have b4_belong_m3: "id_set b4 \<subseteq> snd ?m3"
      using ids_b4 ids_belong_m1 m1_belong_m2 m2_belong_m3 by auto
    have m1_m3: "id_set (fst ?m1) \<inter> id_set (fst ?m3) = {}"
      using overlap_merge finite_m2 ids_m1 m1_belong_m2 b3_belong_m2 b3_m1
      by (simp add: Int_commute)
    have m2_m3: "id_set (fst ?m2) \<inter> id_set (fst ?m3) = {}"
      using overlap_merge finite_m2 ids_m2 b3_belong_m2 b3_m2
      by (simp add: Int_commute)
    have b4_m3: "id_set b4 \<inter> id_set (fst ?m3) = {}"
      using overlap_merge finite_m2 b4_belong_m2 b3_belong_m2 diff_cd
      by (simp add: Int_commute)

    let ?m4 = "merge b4 (snd ?m3)"
    have diff_m4: "diff_ids (fst ?m4)"
      using Node.hyps(4) diff_b4 finite_m3 b4_belong_m3 by auto
    have finite_m4: "finite (snd ?m4)"
      using finite_merge finite_m3 by auto
    have ids_m4: "id_set (fst ?m4) \<subseteq> snd ?m4"
      using ids_merge2 b4_belong_m3 by auto
    have m3_belong_m4: "snd ?m3 \<subseteq> snd ?m4"
      using ids_merge diff_b4 b4_belong_m3 by auto
    have ids_belong_m4: "ids \<subseteq> snd ?m4"
      using ids_belong_m1 m1_belong_m2 m2_belong_m3 m3_belong_m4 by auto
    have m1_m4: "id_set (fst ?m1) \<inter> id_set (fst ?m4) = {}"
      using overlap_merge finite_m3 ids_m1 m1_belong_m2 m2_belong_m3 b4_belong_m3 b4_m1
      by (simp add: Int_commute)
    have m2_m4: "id_set (fst ?m2) \<inter> id_set (fst ?m4) = {}"
      using overlap_merge finite_m3 ids_m2 m2_belong_m3 b4_belong_m3 b4_m2
      by (simp add: Int_commute)
    have m3_m4: "id_set (fst ?m3) \<inter> id_set (fst ?m4) = {}"
      using overlap_merge finite_m3 ids_m3 b4_belong_m3 b4_m3
      by (simp add: Int_commute)

    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson
    have diff_com: "diff_ids (fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)))"
      proof(cases "\<exists>xa xb xc xd. Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))")
        case True
        obtain newid where step1: "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Leaf (FREE, newid)"
          unfolding combine_def Let_def using True by auto
        show ?thesis using step1 diff1 by auto
      next
        case False
        have step2: "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)"
          unfolding combine_def using False by auto
        show ?thesis using step2 diff_m1 diff_m2 diff_m3 diff_m4
          using m1_m2 m1_m3 m1_m4 m2_m3 m2_m4 m3_m4 diff2 by simp
      qed
    have ?case using step diff_com by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma diff_ids_free_branch3:
  "diff_ids_valid bset \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<forall>b\<in>bset. id_set b \<subseteq> ids \<Longrightarrow>
  \<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b) \<Longrightarrow>
  fst (L b) \<noteq> FREE \<Longrightarrow>
  (newbset, newids, re) = free bset b lv ids \<Longrightarrow>
  diff_ids_valid newbset"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "finite ids"
     and a2: "\<forall>b\<in>bset. id_set b \<subseteq> ids"
     and a3: "\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)"
     and a4: "fst (L b) \<noteq> FREE"
     and a5: "(newbset, newids, re) = free bset b lv ids"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_btree: "\<exists>!btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)"
    using a3 diff_bset2
  proof -
    { fix tt :: "(block_state_type \<times> nat) tree" and tta :: "(block_state_type \<times> nat) tree \<Rightarrow> (block_state_type \<times> nat) tree"
      have "\<And>t ta n. t \<notin> bset \<or> ta \<notin> bset \<or> n \<notin> tree.set (tree_map snd t) \<or> n \<notin> tree.set (tree_map snd ta) \<or> ta = t"
        using diff_bset2 id_set_def by auto
      then have "\<exists>t. tt \<notin> bset \<or> tta t \<notin> bset \<or> L b \<notin> tree.set tt \<or> t \<in> bset \<and> tta t = t \<and> L b \<in> tree.set t \<or> t \<in> bset \<and> L b \<in> tree.set t \<and> L b \<notin> tree.set (tta t)"
        by (metis (no_types) image_eqI tree.set_map) }
    then have "\<forall>t. \<exists>ta. \<forall>tb. t \<notin> bset \<or> tb \<notin> bset \<or> L b \<notin> tree.set t \<or> ta \<in> bset \<and> tb = ta \<and> L b \<in> tree.set ta \<or> ta \<in> bset \<and> L b \<in> tree.set ta \<and> L b \<notin> tree.set tb"
      by (metis (no_types))
    then show ?thesis
      by (metis a3)
  qed
  let ?btree = "THE t. t \<in> bset \<and> (L b) \<in> set t \<and> lv = get_level t (L b)"
  have the_btree: "?btree \<in> bset \<and> (L b) \<in> set ?btree \<and> lv = get_level ?btree (L b)"
    using the_P[OF exi_btree] by blast
  have diff_btree: "diff_ids ?btree"
    using the_btree diff_bset1 by auto
  have ids_btree: "id_set ?btree \<subseteq> ids"
    using the_btree a2 by auto
  have exi_newb: "\<exists>newb. newb = replace ?btree b (set_state_type b FREE)"
    by simp
  let ?freeblo = "SOME newb. newb = replace ?btree b (set_state_type b FREE)"
  have diff_freeblo: "diff_ids ?freeblo"
    using diff_ids_replace diff_btree the_btree by simp
  have same_ids: "id_set ?btree = id_set ?freeblo"
    using same_ids_replace diff_btree the_btree by simp
  have exi_re: "\<exists>re. re = merge ?freeblo ids"
    by simp
  let ?re = "SOME re. re = merge ?freeblo ids"
  have diff_newblo: "diff_ids (fst ?re)"
    using diff_ids_merge diff_freeblo a1 ids_btree same_ids by auto
  have overlap_btree: "\<forall>b \<in> bset. b \<noteq> ?btree \<longrightarrow> id_set b \<inter> id_set ?btree = {}"
    using diff_bset2 the_btree by auto
  let ?tembset = "(bset - {?btree}) \<union> {?freeblo}"
  have ids_tembset: "\<forall>b\<in>?tembset. id_set b \<subseteq> ids"
    using a2 ids_btree same_ids by auto
  have overlap_freeblo: "\<forall>b \<in> ?tembset. b \<noteq> ?freeblo \<longrightarrow> id_set b \<inter> id_set ?freeblo = {}"
    using overlap_btree same_ids by auto
  have ids_merge_freeblo: "\<forall>b \<in> ?tembset. b \<noteq> ?freeblo \<longrightarrow> id_set b \<inter> id_set (fst ?re) = {}"
    using overlap_merge a1 ids_tembset overlap_freeblo by auto
(*------------------------------------------------------------------------------------------------*)
  have free_re: "(newbset, newids, re) = ((bset - {?btree}) \<union> {fst ?re}, snd ?re, True)"
    using a4 a5 unfolding free_def Let_def using exi_btree by auto
  have diff_newbset1: "\<forall>b \<in> newbset. diff_ids b"
    using free_re diff_bset1 diff_btree diff_newblo by blast
  have step1: "(\<forall>b1 b2. b1 \<in> (bset - {?btree}) \<and> b2 \<in> (bset - {?btree}) \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using diff_bset2 by auto
  have newstep1: "(\<forall>b1 b2. b1 \<in> (newbset - {fst ?re}) \<and> b2 \<in> (newbset - {fst ?re}) \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using step1 free_re by auto
  have newstep2: "\<forall>b \<in> (newbset - {fst ?re}). id_set b \<inter> id_set (fst ?re) = {}"
    using ids_merge_freeblo free_re
    by (metis (no_types, lifting) DiffE Int_left_absorb UnCI UnE fst_conv id_set_notempty ids_btree inf.orderE overlap_btree same_ids singletonI) 
  have diff_newbset2: "(\<forall>b1 b2. b1 \<in> newbset \<and> b2 \<in> newbset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using newstep1 newstep2 by auto
  show ?thesis using diff_newbset1 diff_newbset2 diff_ids_valid_def by auto
qed

subsection \<open>def and proof of inv_block_free\<close>

inductive block_free :: "Block \<Rightarrow> bool"
  where free1: "block_free (Leaf a)" |
        free2: "block_free ll \<and> block_free lr \<and> block_free rl \<and> block_free rr \<and>
                \<not> (\<exists>xa xb xc xd. (Node ll lr rl rr) = (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))
                \<Longrightarrow> block_free (Node ll lr rl rr)"

inductive_cases block_free_leaf_node:
  "block_free (Leaf a)"
  "block_free (Node ll lr rl rr)"

definition "block_free_valid bset \<equiv> (\<forall>b \<in> bset. block_free b)"

lemma block_free_free_branch1:
  "block_free_valid bset \<Longrightarrow>
  \<not> (\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)) \<Longrightarrow>
  block_free_valid (fst (free bset b lv ids))"
  unfolding free_def Let_def by auto

lemma block_free_free_branch2:
  "block_free_valid bset \<Longrightarrow>
  \<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b) \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  block_free_valid (fst (free bset b lv ids))"
  unfolding free_def Let_def by auto

lemma block_free_merge:
  "block_free (fst (merge B ids))"
proof(induct B arbitrary: ids)
case (Leaf x)
  then show ?case using free1 by auto
next
  case (Node b1 b2 b3 b4)
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    obtain newid where com: "fst (combine (Node b1 b2 b3 b4) ids) = Leaf (FREE, newid)"
      unfolding combine_def Let_def using fst_conv a0 by auto
    then have ?case using step free1 by auto
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have free_m1: "block_free (fst ?m1)"
      using Node.hyps(1) by auto
    let ?m2 = "merge b2 (snd ?m1)"
    have free_m2: "block_free (fst ?m2)"
      using Node.hyps(2) by auto
    let ?m3 = "merge b3 (snd ?m2)"
    have free_m3: "block_free (fst ?m3)"
      using Node.hyps(3) by auto
    let ?m4 = "merge b4 (snd ?m3)"
    have free_m4: "block_free (fst ?m4)"
      using Node.hyps(4) by auto
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson
    have free_com: "block_free (fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)))"
      proof(cases "\<exists>xa xb xc xd. Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))")
        case True
        obtain newid where step1: "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Leaf (FREE, newid)"
          unfolding combine_def Let_def using True by auto
        show ?thesis using step1 free1 by auto
      next
        case False
        have step2: "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)"
          unfolding combine_def using False by auto
        show ?thesis using step2 free_m1 free_m2 free_m3 free_m4 False free2 by auto
      qed
    have ?case using step free_com by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma block_free_free_branch3:
  "diff_ids_valid bset \<Longrightarrow>
  block_free_valid bset \<Longrightarrow>
  \<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b) \<Longrightarrow>
  fst (L b) \<noteq> FREE \<Longrightarrow>
  (newbset, newids, re) = free bset b lv ids \<Longrightarrow>
  block_free_valid newbset"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "block_free_valid bset"
     and a2: "\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)"
     and a3: "fst (L b) \<noteq> FREE"
     and a4: "(newbset, newids, re) = free bset b lv ids"
  have diff_bset: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have free_bset: "(\<forall>b \<in> bset. block_free b)"
    using a1 block_free_valid_def by auto
  have exi_btree: "\<exists>!btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)"
    using a1 diff_bset
    proof -
      { fix tt :: "(block_state_type \<times> nat) tree" and tta :: "(block_state_type \<times> nat) tree \<Rightarrow> (block_state_type \<times> nat) tree"
        have "\<And>t ta n. t \<notin> bset \<or> ta \<notin> bset \<or> n \<notin> tree.set (tree_map snd t) \<or> n \<notin> tree.set (tree_map snd ta) \<or> ta = t"
          using diff_bset id_set_def by auto
        then have "\<exists>t. tt \<notin> bset \<or> tta t \<notin> bset \<or> L b \<notin> tree.set tt \<or> t \<in> bset \<and> tta t = t \<and> L b \<in> tree.set t \<or> t \<in> bset \<and> L b \<in> tree.set t \<and> L b \<notin> tree.set (tta t)"
          by (metis (no_types) image_eqI tree.set_map) }
      then have "\<forall>t. \<exists>ta. \<forall>tb. t \<notin> bset \<or> tb \<notin> bset \<or> L b \<notin> tree.set t \<or> ta \<in> bset \<and> tb = ta \<and> L b \<in> tree.set ta \<or> ta \<in> bset \<and> L b \<in> tree.set ta \<and> L b \<notin> tree.set tb"
        by (metis (no_types))
      then show ?thesis
        by (metis a2)
    qed
    let ?btree = "THE t. t \<in> bset \<and> (L b) \<in> set t \<and> lv = get_level t (L b)"
  have the_btree: "?btree \<in> bset \<and> (L b) \<in> set ?btree \<and> lv = get_level ?btree (L b)"
    using the_P[OF exi_btree] by blast
  have free_btree: "block_free ?btree"
    using the_btree free_bset by auto
  have exi_newb: "\<exists>newb. newb = replace ?btree b (set_state_type b FREE)"
    by simp
  let ?freeblo = "SOME newb. newb = replace ?btree b (set_state_type b FREE)"
  have exi_re: "\<exists>re. re = merge ?freeblo ids"
    by simp
  let ?re = "SOME re. re = merge ?freeblo ids"
  have free_newblo: "block_free (fst ?re)"
    using block_free_merge by auto
  have free_re: "(newbset, newids, re) = ((bset - {?btree}) \<union> {fst ?re}, snd ?re, True)"
    using a3 a4 unfolding free_def Let_def using exi_btree by auto
  have free_newbset: "(\<forall>b \<in> newbset. block_free b)"
    using free_re free_bset free_btree free_newblo by auto
  show ?thesis using free_newbset block_free_valid_def by auto
qed

lemma block_free_alloc_fail:
  "block_free_valid bset \<Longrightarrow>
  \<not> (exists_freelevel bset lv) \<Longrightarrow>
  block_free_valid (fst (alloc bset lv ids))"
  unfolding alloc_def Let_def by auto

lemma block_free_replace_alloc:
  "diff_ids B \<Longrightarrow>
  block_free B \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b ALLOC \<Longrightarrow>
  block_free (replace B b b')"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(3) by fastforce
  have leaf_b': "b' = Leaf (ALLOC, snd x)"
    using Leaf.prems(4) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B': "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
    using leaf_b leaf_b' unfolding replace_def by auto
  then show ?case using free1 by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have free_b1: "block_free b1"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_b2: "block_free b2"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_b3: "block_free b3"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_b4: "block_free b4"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_node: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))"
    using Node.prems(2) block_free_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(4) apply auto[1]
      using no_replace no_belong_b3 Node.prems(4) apply auto[1]
      using no_replace no_belong_b4 Node.prems(4) by auto
    have free_b1': "block_free (replace b1 b b')"
      using Node.hyps(1) diff_b1 free_b1 a0 Node.prems(4) by auto
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node (replace b1 b b') b2 b3 b4) = (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))"
    proof-
      {assume c10: "leaf b1"
        obtain x where c11: "b1 = Leaf x" using c10
          by (metis tree.collapse(1)) 
        have leaf_b: "L b = x"
          using a0 c11 by fastforce
        have leaf_b': "b' = Leaf (ALLOC, snd x)"
          using Node.prems(4) leaf_b unfolding set_state_type_def Let_def by auto
        have leaf_B': "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
          using leaf_b leaf_b' unfolding replace_def by auto
        have ?thesis using leaf_B' by (simp add: c11) 
      }moreover
      {assume c20: "\<not> leaf b1"
        have node_b1: "node b1"
          using c20 tree.exhaust_disc by auto 
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using node_b1
          by (metis tree.collapse(2))
        have node_replace: "node (replace (Node m1 m2 m3 m4) b b')"
          unfolding replace_def by auto
        have ?thesis using node_replace c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using replace_re free_b1' free_b2 free_b3 free_b4 free_node' free2 by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(4) apply auto[1]
      using no_replace no_belong_b3 Node.prems(4) apply auto[1]
      using no_replace no_belong_b4 Node.prems(4) by auto
    have free_b2': "block_free (replace b2 b b')"
      using Node.hyps(2) diff_b2 free_b2 a1 Node.prems(4) by auto
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node b1 (replace b2 b b') b3 b4) = (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))"
    proof-
      {assume c10: "leaf b2"
        obtain x where c11: "b2 = Leaf x" using c10
          by (metis tree.collapse(1)) 
        have leaf_b: "L b = x"
          using a1 c11 by fastforce
        have leaf_b': "b' = Leaf (ALLOC, snd x)"
          using Node.prems(4) leaf_b unfolding set_state_type_def Let_def by auto
        have leaf_B': "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
          using leaf_b leaf_b' unfolding replace_def by auto
        have ?thesis using leaf_B' by (simp add: c11) 
      }moreover
      {assume c20: "\<not> leaf b2"
        have node_b1: "node b2"
          using c20 tree.exhaust_disc by auto 
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using node_b1
          by (metis tree.collapse(2))
        have node_replace: "node (replace (Node m1 m2 m3 m4) b b')"
          unfolding replace_def by auto
        have ?thesis using node_replace c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using replace_re free_b1 free_b2' free_b3 free_b4 free_node' free2 by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(4) apply auto[1]
      using no_replace no_belong_b2 Node.prems(4) apply auto[1]
      using no_replace no_belong_b4 Node.prems(4) by auto
    have free_b3': "block_free (replace b3 b b')"
      using Node.hyps(3) diff_b3 free_b3 a2 Node.prems(4) by auto
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node b1 b2 (replace b3 b b') b4) = (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))"
    proof-
      {assume c10: "leaf b3"
        obtain x where c11: "b3 = Leaf x" using c10
          by (metis tree.collapse(1)) 
        have leaf_b: "L b = x"
          using a2 c11 by fastforce
        have leaf_b': "b' = Leaf (ALLOC, snd x)"
          using Node.prems(4) leaf_b unfolding set_state_type_def Let_def by auto
        have leaf_B': "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
          using leaf_b leaf_b' unfolding replace_def by auto
        have ?thesis using leaf_B' by (simp add: c11) 
      }moreover
      {assume c20: "\<not> leaf b3"
        have node_b1: "node b3"
          using c20 tree.exhaust_disc by auto 
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using node_b1
          by (metis tree.collapse(2))
        have node_replace: "node (replace (Node m1 m2 m3 m4) b b')"
          unfolding replace_def by auto
        have ?thesis using node_replace c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using replace_re free_b1 free_b2 free_b3' free_b4 free_node' free2 by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(4) apply auto[1]
      using no_replace no_belong_b2 Node.prems(4) apply auto[1]
      using no_replace no_belong_b3 Node.prems(4) by auto
    have free_b4': "block_free (replace b4 b b')"
      using Node.hyps(4) diff_b4 free_b4 a3 Node.prems(4) by auto
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 (replace b4 b b')) = (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))"
    proof-
      {assume c10: "leaf b4"
        obtain x where c11: "b4 = Leaf x" using c10
          by (metis tree.collapse(1)) 
        have leaf_b: "L b = x"
          using a3 c11 by fastforce
        have leaf_b': "b' = Leaf (ALLOC, snd x)"
          using Node.prems(4) leaf_b unfolding set_state_type_def Let_def by auto
        have leaf_B': "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
          using leaf_b leaf_b' unfolding replace_def by auto
        have ?thesis using leaf_B' by (simp add: c11) 
      }moreover
      {assume c20: "\<not> leaf b4"
        have node_b1: "node b4"
          using c20 tree.exhaust_disc by auto 
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using node_b1
          by (metis tree.collapse(2))
        have node_replace: "node (replace (Node m1 m2 m3 m4) b b')"
          unfolding replace_def by auto
        have ?thesis using node_replace c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using replace_re free_b1 free_b2 free_b3 free_b4' free_node' free2 by auto
  }
  ultimately have ?case using Node.prems(3) by fastforce
  then show ?case by auto
qed

lemma block_free_alloc_branch1:
  "diff_ids_valid bset \<Longrightarrow>
  block_free_valid bset \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax = lv \<Longrightarrow>
  (newbset, newids, re, reid) = alloc1 bset lv ids \<Longrightarrow>
  block_free_valid newbset"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "block_free_valid bset"
     and a2: "exists_freelevel bset lv"
     and a3: "lmax = freesets_maxlevel bset lv"
     and a4: "lmax = lv"
     and a5: "(newbset, newids, re, reid) = alloc1 bset lv ids"
  have diff_bset: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have free_bset: "(\<forall>b \<in> bset. block_free b)"
    using a1 block_free_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a2 by auto
  have eq_lv: "lv = (THE lmax. lmax \<le> lv \<and>
                    freesets_level_pool bset lmax \<noteq> {} \<and>
                    (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a3 a4 unfolding freesets_maxlevel_def by auto
  have the_lv: "lv \<le> lv \<and>
               freesets_level_pool bset lv \<noteq> {} \<and>
               (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lv)"
    using the_P[OF exi_lmax eq_lv] by auto
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
    using the_lv unfolding freesets_level_pool_def by auto
  let ?blo = "SOME b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
  have diff_blo: "diff_ids ?blo"
    using diff_bset exi_b
    by (metis (mono_tags, lifting) some_eq_ex) 
  have free_blo: "block_free ?blo"
    using free_bset exi_b
    by (metis (mono_tags, lifting) some_eq_ex) 
  have exi_l: "\<exists>l. l \<in> freesets_level ?blo lv"
    using someI_ex[OF exi_b] by auto
  let ?l = "SOME l. l \<in> freesets_level ?blo lv"
  have leaf_belong: "L ?l \<in> set ?blo"
    using exi_l unfolding freesets_level_def freesets_def
    by (metis (no_types, lifting) CollectD someI_ex) 
  have exi_newb: "\<exists>newb. newb = replace ?blo ?l (set_state_type ?l ALLOC)"
    by simp
  let ?newb = "SOME newb. newb = replace ?blo ?l (set_state_type ?l ALLOC)"
  have free_newblo: "block_free ?newb"
    using block_free_replace_alloc diff_blo free_blo leaf_belong by simp
  have alloc1_re: "(newbset, newids, re, reid) = (((bset - {?blo}) \<union> {?newb}), ids, True, {snd (L ?l)})"
    using a5 unfolding alloc1_def by (metis some_eq_trivial) 
  have free_newbset: "\<forall>b \<in> newbset. block_free b"
    using alloc1_re free_bset free_blo free_newblo by blast
  show ?thesis using free_newbset block_free_valid_def by auto
qed

lemma block_free_split:
  "lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (L b) \<in> ids \<Longrightarrow>
  block_free (fst (split b ids (lv - lmax)))"
proof(induct "lv - lmax" arbitrary: lmax b ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and alloc_ll: "fst ll = ALLOC"
    unfolding divide_def Let_def by auto
  let ?newids = "snd (divide b ids)"
  have belong_ll: "snd ll \<in> ?newids"
    using divide_belong pdivide by auto
  have step': "fst (split b ids (lv - lmax)) = Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
    using split_induct Suc(3) pdivide by (meson zero_less_diff)
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_lmax: "lv = Suc lmax"
      using Suc(2) xa_eq_1 by linarith
    have split_ll: "fst (split (Leaf ll) ?newids (lv - lmax - 1)) = Leaf ll"
      using lv_suc_lmax by auto
    have step1: "fst (split b ids (lv - lmax)) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      using step' split_ll by auto
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) =
                     (Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))))"
      using alloc_ll by auto
    have free_node: "block_free (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr))"
      using free1 free2 free_node' by auto
    have ?case using step1 free_node by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_lmax: "xa = lv - Suc lmax"
      using Suc(2) by linarith
    have suc_lmax_less_lv: "Suc lmax < lv"
      using Suc(3) xa_gr_1 xa_lv_suc_lmax by linarith
    have split2: "block_free (fst (split (Leaf ll) ?newids (lv - Suc lmax)))"
      using Suc(1) xa_lv_suc_lmax suc_lmax_less_lv divide_finite Suc(4) belong_ll pdivide by auto
    have node_split: "node (fst (split (Leaf ll) ?newids (lv - Suc lmax)))"
      using split.simps suc_lmax_less_lv
      by (metis diff_is_0_eq fst_conv leD tree.disc(4)) 
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr)) = 
                     Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
      using node_split by auto
    have free_node: "block_free (Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr))"
      using free1 free2 split2 free_node' by auto
    have ?case using step' free_node by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma block_free_replace_leaf:
  "diff_ids blo \<Longrightarrow>
  block_free blo \<Longrightarrow>
  lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_set blo \<subseteq> ids \<Longrightarrow>
  L b \<in> tree.set blo \<Longrightarrow>
  block_free (replace_leaf blo b (fst (split b ids (lv - lmax))))"
proof(induct blo)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(6) by fastforce
  have b_belong: "snd (L b) \<in> ids"
    using Leaf.prems(5) leaf_b unfolding id_set_def by auto
  have free_b_split: "block_free (fst (split b ids (lv - lmax)))"
    using block_free_split Leaf.prems(3,4) b_belong by auto
  have replace_leaf_step: "replace_leaf (Leaf x) b (fst (split b ids (lv - lmax))) = fst (split b ids (lv - lmax))"
    using leaf_b replace_leaf.simps(1) by auto
  show ?case using replace_leaf_step free_b_split by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have free_b1: "block_free b1"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_b2: "block_free b2"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_b3: "block_free b3"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have free_b4: "block_free b4"
    using Node.prems(2) block_free_leaf_node(2) by blast
  have node_split: "node (fst (split b ids (lv - lmax)))"
      using split.simps Node.prems(3)
      by (metis diff_is_0_eq fst_conv leD tree.disc(4))
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node (replace_leaf b1 b (fst (split b ids (lv - lmax)))) b2 b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b2 no_belong_b3 no_belong_b4 by auto
    have free_b1': "block_free (replace_leaf b1 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(1) diff_b1 free_b1 Node.prems(3,4,5) a0 unfolding id_set_def by fastforce
    have node_replace_leaf: "node (replace_leaf b1 b (fst (split b ids (lv - lmax))))"
      using replace_leaf.simps node_split
      by (metis Node.prems(1) a0 diff_node4 order_refl replace_subbtr_belong tree.discI(2) tree.exhaust)
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node (replace_leaf b1 b (fst (split b ids (lv - lmax)))) b2 b3 b4) = 
                     Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
      using node_replace_leaf by auto
    have free_node: "block_free (Node (replace_leaf b1 b (fst (split b ids (lv - lmax)))) b2 b3 b4)"
      using free1 free2 free_b1' free_b2 free_b3 free_b4 free_node' by auto
    have ?case using replace_leaf_step free_node by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node b1 (replace_leaf b2 b (fst (split b ids (lv - lmax)))) b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b3 no_belong_b4 by auto
    have free_b2': "block_free (replace_leaf b2 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(2) diff_b2 free_b2 Node.prems(3,4,5) a1 unfolding id_set_def by fastforce
    have node_replace_leaf: "node (replace_leaf b2 b (fst (split b ids (lv - lmax))))"
      using replace_leaf.simps node_split
      by (metis Node.prems(1) a1 diff_node4 order_refl replace_subbtr_belong tree.discI(2) tree.exhaust)
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node b1 (replace_leaf b2 b (fst (split b ids (lv - lmax)))) b3 b4) = 
                     Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
      using node_replace_leaf by auto
    have free_node: "block_free (Node b1 (replace_leaf b2 b (fst (split b ids (lv - lmax)))) b3 b4)"
      using free1 free2 free_b1 free_b2' free_b3 free_b4 free_node' by auto
    have ?case using replace_leaf_step free_node by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node b1 b2 (replace_leaf b3 b (fst (split b ids (lv - lmax)))) b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b4 by auto
    have free_b3': "block_free (replace_leaf b3 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(3) diff_b3 free_b3 Node.prems(3,4,5) a2 unfolding id_set_def by fastforce
    have node_replace_leaf: "node (replace_leaf b3 b (fst (split b ids (lv - lmax))))"
      using replace_leaf.simps node_split
      by (metis Node.prems(1) a2 diff_node4 order_refl replace_subbtr_belong tree.discI(2) tree.exhaust)
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node b1 b2 (replace_leaf b3 b (fst (split b ids (lv - lmax)))) b4) = 
                     Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
      using node_replace_leaf by auto
    have free_node: "block_free (Node b1 b2 (replace_leaf b3 b (fst (split b ids (lv - lmax)))) b4)"
      using free1 free2 free_b1 free_b2 free_b3' free_b4 free_node' by auto
    have ?case using replace_leaf_step free_node by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b (fst (split b ids (lv - lmax))) =
                            Node b1 b2 b3 (replace_leaf b4 b (fst (split b ids (lv - lmax))))"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b3 by auto
    have free_b4': "block_free (replace_leaf b4 b (fst (split b ids (lv - lmax))))"
      using Node.hyps(4) diff_b4 free_b4 Node.prems(3,4,5) a3 unfolding id_set_def by fastforce
    have node_replace_leaf: "node (replace_leaf b4 b (fst (split b ids (lv - lmax))))"
      using replace_leaf.simps node_split
      by (metis Node.prems(1) a3 diff_node4 order_refl replace_subbtr_belong tree.discI(2) tree.exhaust)
    have free_node': "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 (replace_leaf b4 b (fst (split b ids (lv - lmax))))) = 
                     Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
      using node_replace_leaf by auto
    have free_node: "block_free (Node b1 b2 b3 (replace_leaf b4 b (fst (split b ids (lv - lmax)))))"
      using free1 free2 free_b1 free_b2 free_b3 free_b4' free_node' by auto
    have ?case using replace_leaf_step free_node by auto
  }
  ultimately have ?case
    using Node.prems(6) by fastforce
  then show ?case by auto
qed

lemma block_free_alloc_branch2:
  "diff_ids_valid bset \<Longrightarrow>
  block_free_valid bset \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<forall>b\<in>bset. id_set b \<subseteq> ids \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax \<noteq> lv \<Longrightarrow>
  blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {}) \<Longrightarrow>
  b = (SOME l. l \<in> freesets_level blo lmax) \<Longrightarrow>
  (subbtr, ids') = split b ids (lv - lmax) \<Longrightarrow>
  newbtr = replace_leaf blo b subbtr \<Longrightarrow>
  newbset = bset - {blo} \<union> {newbtr} \<Longrightarrow>
  block_free_valid newbset"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "block_free_valid bset"
     and a2: "finite ids"
     and a3: "\<forall>b\<in>bset. id_set b \<subseteq> ids"
     and a4: "exists_freelevel bset lv"
     and a5: "lmax = freesets_maxlevel bset lv"
     and a6: "lmax \<noteq> lv"
     and a7: "blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {})"
     and a8: "b = (SOME l. l \<in> freesets_level blo lmax)"
     and a9: "(subbtr, ids') = split b ids (lv - lmax)"
     and a10: "newbtr = replace_leaf blo b subbtr"
     and a11: "newbset = bset - {blo} \<union> {newbtr}"
  have diff_bset: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have free_bset: "(\<forall>b \<in> bset. block_free b)"
    using a1 block_free_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a4 by auto
  have eq_lmax: "lmax = (THE lmax. lmax \<le> lv \<and>
                        freesets_level_pool bset lmax \<noteq> {} \<and>
                        (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a5 unfolding freesets_maxlevel_def by auto
  have the_lmax: "lmax < lv \<and>
                 freesets_level_pool bset lmax \<noteq> {} \<and>
                 (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using the_P[OF exi_lmax eq_lmax] a6 by auto
  have lmax_le_lv: "lmax < lv" using the_lmax by auto
(*------------------------------------------------------------------------------------------------*)
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lmax \<noteq> {}"
    using the_lmax unfolding freesets_level_pool_def by auto
  have exi_blo: "blo \<in> bset \<and> freesets_level blo lmax \<noteq> {}"
    using someI_ex[OF exi_b] a7 by auto
  have diff_blo: "diff_ids blo"
    using diff_bset exi_blo by auto
  have free_blo: "block_free blo"
    using free_bset exi_blo by auto
  have ids_blo: "id_set blo \<subseteq> ids"
    using a3 exi_blo by auto
  have exi_l: "\<exists>l. l \<in> freesets_level blo lmax"
    using exi_blo by auto
  have exi_b: "b \<in> freesets_level blo lmax"
    using someI_ex[OF exi_l] a8 by auto
  have b_belong_blo: "L b \<in> tree.set blo"
    using exi_b unfolding freesets_level_def freesets_def by auto
(*------------------------------------------------------------------------------------------------*)
  have free_newbtr: "block_free newbtr"
    using block_free_replace_leaf diff_blo free_blo lmax_le_lv a2 ids_blo b_belong_blo a9 a10 fst_conv by metis
  have free_newbset': "\<forall>b \<in> newbset. block_free b"
    using a11 free_bset free_blo free_newbtr by blast
  have free_newbset: "block_free_valid newbset"
    using free_newbset' block_free_valid_def by auto
  then show ?thesis by auto
qed

subsection \<open>def and proof of inv_block_leak\<close>

fun get_node :: "Block \<Rightarrow> Block set"
  where "get_node (Leaf x) = {}" |
        "get_node (Node n1 n2 n3 n4) = get_node n1 \<union> get_node n2 \<union> get_node n3 \<union> get_node n4 \<union> {(Node n1 n2 n3 n4)}"

definition quadtree :: "Block \<Rightarrow> bool"
  where "quadtree b \<equiv> card (set b) = Suc (card (get_node b) * 3)"

lemma get_node_set:
  "x \<in> get_node b \<Longrightarrow>
  set x \<subseteq> set b"
  apply(induct b)
  by auto

lemma get_node_notbelong:
  "set oth \<inter> set (Node b1 b2 b3 b4) = {} \<Longrightarrow>
  get_node oth \<noteq> {} \<Longrightarrow>
  (Node b1 b2 b3 b4) \<notin> get_node oth"
proof(induct oth arbitrary: b1 b2 b3 b4)
  case (Leaf x)
  then show ?case by auto
next
  case (Node oth1 oth2 oth3 oth4)
  have oth1_node: "set oth1 \<inter> set (Node b1 b2 b3 b4) = {}"
    using Node.prems(1) by auto
  have oth2_node: "set oth2 \<inter> set (Node b1 b2 b3 b4) = {}"
    using Node.prems(1) by auto
  have oth3_node: "set oth3 \<inter> set (Node b1 b2 b3 b4) = {}"
    using Node.prems(1) by auto
  have oth4_node: "set oth4 \<inter> set (Node b1 b2 b3 b4) = {}"
    using Node.prems(1) by auto
  have oth_node: "(Node b1 b2 b3 b4) \<notin> {(Node oth1 oth2 oth3 oth4)}"
    using Node.prems(1)
    by (metis Int_absorb Node.hyps(1) UnCI all_not_in_conv get_node.elims insert_not_empty singletonD tree.set_intros(2) tree.simps(15)) 
  have not_belong_oth1: "(Node b1 b2 b3 b4) \<notin> get_node oth1"
    proof(cases "get_node oth1 = {}")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis using Node.hyps(1) oth1_node by auto
    qed
  have not_belong_oth2: "(Node b1 b2 b3 b4) \<notin> get_node oth2"
    proof(cases "get_node oth2 = {}")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis using Node.hyps(2) oth2_node by auto
    qed
  have not_belong_oth3: "(Node b1 b2 b3 b4) \<notin> get_node oth3"
    proof(cases "get_node oth3 = {}")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis using Node.hyps(3) oth3_node by auto
    qed
  have not_belong_oth4: "(Node b1 b2 b3 b4) \<notin> get_node oth4"
    proof(cases "get_node oth4 = {}")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis using Node.hyps(4) oth4_node by auto
    qed
  have step: "get_node (Node oth1 oth2 oth3 oth4) = get_node oth1 \<union> get_node oth2 \<union> get_node oth3 \<union> get_node oth4 \<union> {(Node oth1 oth2 oth3 oth4)}"
    using get_node.simps(2) by auto
  have not_belong_step: "(Node b1 b2 b3 b4) \<notin> (get_node oth1 \<union> get_node oth2 \<union> get_node oth3 \<union> get_node oth4 \<union> {(Node oth1 oth2 oth3 oth4)})"
    using oth_node not_belong_oth1 not_belong_oth2 not_belong_oth3 not_belong_oth4 by auto
  show ?case using step not_belong_step by auto
qed

lemma get_node_overlap:
  "set oth \<inter> set B = {} \<Longrightarrow>
  get_node oth \<noteq> {} \<Longrightarrow>
  get_node B \<noteq> {} \<Longrightarrow>
  get_node oth \<inter> get_node B = {}"
proof(induct B arbitrary: oth)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have oth_b1: "set oth \<inter> set b1 = {}"
    using Node.prems(1) by auto
  have oth_b2: "set oth \<inter> set b2 = {}"
    using Node.prems(1) by auto
  have oth_b3: "set oth \<inter> set b3 = {}"
    using Node.prems(1) by auto
  have oth_b4: "set oth \<inter> set b4 = {}"
    using Node.prems(1) by auto
  have oth_node: "oth \<noteq> Node b1 b2 b3 b4"
    using Node.prems(1)
    by (metis Node.hyps(4) empty_iff equals0I get_node.simps(2) inf.idem insert_not_empty sup_eq_bot_iff tree.exhaust tree.set_intros(5) tree.simps(15)) 
  have oth_b1_overlap: "get_node oth \<inter> get_node b1 = {}"
    proof(cases "get_node b1 = {}")
    case True
      then show ?thesis using Node.prems(2) by auto
    next
    case False
      then show ?thesis using Node.hyps(1) oth_b1 Node.prems(2) by auto
    qed
  have oth_b2_overlap: "get_node oth \<inter> get_node b2 = {}"
    proof(cases "get_node b2 = {}")
    case True
      then show ?thesis using Node.prems(2) by auto
    next
    case False
      then show ?thesis using Node.hyps(2) oth_b2 Node.prems(2) by auto
    qed
  have oth_b3_overlap: "get_node oth \<inter> get_node b3 = {}"
    proof(cases "get_node b3 = {}")
    case True
      then show ?thesis using Node.prems(2) by auto
    next
    case False
      then show ?thesis using Node.hyps(3) oth_b3 Node.prems(2) by auto
    qed
  have oth_b4_overlap: "get_node oth \<inter> get_node b4 = {}"
    proof(cases "get_node b4 = {}")
    case True
      then show ?thesis using Node.prems(2) by auto
    next
    case False
      then show ?thesis using Node.hyps(4) oth_b4 Node.prems(2) by auto
    qed
  have oth_node_overlap: "get_node oth \<inter> {Node b1 b2 b3 b4} = {}"
    using get_node_notbelong Node.prems(1,2) by auto
  have step: "get_node (Node b1 b2 b3 b4) = get_node b1 \<union> get_node b2 \<union> get_node b3 \<union> get_node b4 \<union> {(Node b1 b2 b3 b4)}"
    using get_node.simps(2) by auto
  have step_overlap: "get_node oth \<inter> (get_node b1 \<union> get_node b2 \<union> get_node b3 \<union> get_node b4 \<union> {(Node b1 b2 b3 b4)}) = {}"
    using oth_b1_overlap oth_b2_overlap oth_b3_overlap oth_b4_overlap oth_node_overlap by auto
  show ?case using step step_overlap by auto
qed

lemma get_node_card:
  "set b1 \<inter> set b2 = {} \<Longrightarrow>
  finite (get_node b1) \<Longrightarrow>
  finite (get_node b2) \<Longrightarrow>
  card (get_node b1 \<union> get_node b2) = card (get_node b1) + card (get_node b2)"
proof-
  assume a0: "set b1 \<inter> set b2 = {}"
     and a1: "finite (get_node b1)"
     and a2: "finite (get_node b2)"
  {assume b0: "get_node b1 = {} \<and> get_node b2 = {}"
    then have ?thesis by auto
  }
  moreover
  {assume b1: "get_node b1 = {} \<and> get_node b2 \<noteq> {}"
    then have ?thesis by simp
  }
  moreover
  {assume b2: "get_node b1 \<noteq> {} \<and> get_node b2 = {}"
    then have ?thesis by simp
  }
  moreover
  {assume b3: "get_node b1 \<noteq> {} \<and> get_node b2 \<noteq> {}"
    have b1_b2_overlap: "get_node b1 \<inter> get_node b2 = {}"
      using get_node_overlap a0 b3 by auto
    have ?thesis using b3 a1 a2 b1_b2_overlap
      by (simp add: card_Un_disjoint) 
  }
  ultimately have ?thesis by blast
  then show ?thesis by auto
qed

lemma is_quadtree:
  "diff_ids B \<Longrightarrow>
  quadtree B"
proof(induct B)
case (Leaf x)
  then show ?case unfolding quadtree_def by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have set_ab: "set b1 \<inter> set b2 = {}"
    using diff_ab unfolding id_set_def
    by (metis Node.prems diff_leaf1 disjoint_iff_not_equal tree.sel(1))
  have set_ac: "set b1 \<inter> set b3 = {}"
    using diff_ab unfolding id_set_def
    by (metis Node.prems diff_leaf1 disjoint_iff_not_equal tree.sel(1))
  have set_ad: "set b1 \<inter> set b4 = {}"
    using diff_ab unfolding id_set_def
    by (metis Node.prems diff_leaf1 disjoint_iff_not_equal tree.sel(1))
  have set_bc: "set b2 \<inter> set b3 = {}"
    using diff_ab unfolding id_set_def
    by (metis Node.prems diff_leaf2 disjoint_iff_not_equal tree.sel(1))
  have set_bd: "set b2 \<inter> set b4 = {}"
    using diff_ab unfolding id_set_def
   by (metis Node.prems diff_leaf2 disjoint_iff_not_equal tree.sel(1))
  have set_cd: "set b3 \<inter> set b4 = {}"
    using diff_ab unfolding id_set_def
    by (metis Node.prems diff_leaf3 disjoint_iff_not_equal tree.sel(1))
  have quad_b1': "quadtree b1"
    using Node.hyps(1) diff_b1 by auto
  have quad_b1: "card (set b1) = Suc (card (get_node b1) * 3)"
    using quad_b1' unfolding quadtree_def by auto
  have quad_b2': "quadtree b2"
    using Node.hyps(2) diff_b2 by auto
  have quad_b2: "card (set b2) = Suc (card (get_node b2) * 3)"
    using quad_b2' unfolding quadtree_def by auto
  have quad_b3': "quadtree b3"
    using Node.hyps(3) diff_b3 by auto
  have quad_b3: "card (set b3) = Suc (card (get_node b3) * 3)"
    using quad_b3' unfolding quadtree_def by auto
  have quad_b4': "quadtree b4"
    using Node.hyps(4) diff_b4 by auto
  have quad_b4: "card (set b4) = Suc (card (get_node b4) * 3)"
    using quad_b4' unfolding quadtree_def by auto
  have card_set_step: "card (set (Node b1 b2 b3 b4)) = card (set b1) + card (set b2) + card (set b3) + card (set b4)"
    using set_ab set_ac set_ad set_bc set_bd set_cd
    proof -
      have f1: "\<forall>P. (tree.set b1 \<union> P) \<inter> tree.set b3 = {} \<union> P \<inter> tree.set b3"
        by (simp add: Int_Un_distrib2 set_ac)
      have f2: "\<forall>P. (P \<union> tree.set b3) \<inter> tree.set b4 = P \<inter> tree.set b4"
        by (metis Int_Un_distrib2 set_cd sup_bot.right_neutral)
    have f3: "\<forall>P. (tree.set b1 \<union> P) \<inter> tree.set b4 = {} \<union> P \<inter> tree.set b4"
      by (metis Int_Un_distrib2 set_ad)
    have "((finite (tree.set b2) \<and> finite (tree.set b1)) \<and> finite (tree.set b4)) \<and> finite (tree.set b3)"
      by (metis (no_types) card.infinite nat.distinct(1) quad_b1 quad_b2 quad_b3 quad_b4)
    then show ?thesis
      using f3 f2 f1 by (simp add: card_Un_disjoint set_ab set_bc set_bd)
  qed
  have f_node_b1: "finite (get_node b1)"
    apply(induct b1) by auto
  have f_node_b2: "finite (get_node b2)"
    apply(induct b2) by auto
  have f_node_b3: "finite (get_node b3)"
    apply(induct b3) by auto
  have f_node_b4: "finite (get_node b4)"
    apply(induct b4) by auto
  have card_node_step: "get_node (Node b1 b2 b3 b4) = get_node b1 \<union> get_node b2 \<union> get_node b3 \<union> get_node b4 \<union> {(Node b1 b2 b3 b4)}"
    using get_node.simps(2) by auto
  have card_node': "card (get_node b1 \<union> get_node b2 \<union> get_node b3 \<union> get_node b4) = card (get_node b1) + card (get_node b2) + card (get_node b3) + card (get_node b4)"
    using get_node_card set_ab set_ac set_ad set_bc set_bd set_cd f_node_b1 f_node_b2 f_node_b3 f_node_b4
    proof -
      have f1: "get_node b4 = {} \<or> get_node b3 = {} \<or> get_node b3 \<inter> get_node b4 = {}"
        by (meson get_node_overlap set_cd)
      have f2: "get_node b4 = {} \<or> get_node b1 = {} \<or> get_node b1 \<inter> get_node b4 = {}"
        using get_node_overlap set_ad by auto
      have f3: "get_node b3 = {} \<or> get_node b1 = {} \<or> get_node b1 \<inter> get_node b3 = {}"
        by (metis get_node_overlap set_ac)
      have f4: "({}::(block_state_type \<times> nat) tree set) \<union> {} = {}"
        by blast
      have f5: "\<And>T. get_node b4 = {} \<or> get_node b2 = {} \<or> (T \<union> get_node b2) \<inter> get_node b4 = T \<inter> get_node b4 \<union> {}"
        by (metis (no_types) Int_Un_distrib2 get_node_overlap set_bd)
      have f6: "\<And>T. get_node b3 = {} \<or> get_node b2 = {} \<or> (T \<union> get_node b2) \<inter> get_node b3 = T \<inter> get_node b3 \<union> {}"
        by (metis (no_types) Int_Un_distrib2 get_node_overlap set_bc)
      moreover
      { assume "get_node b4 \<noteq> {} \<and> get_node b3 \<noteq> {}"
        moreover
        { assume "get_node b2 \<noteq> {} \<and> get_node b4 \<noteq> {} \<and> get_node b3 \<noteq> {}"
          then have "get_node b1 \<noteq> {} \<and> get_node b2 \<noteq> {} \<and> get_node b4 \<noteq> {} \<and> get_node b3 \<noteq> {} \<or> get_node b1 \<inter> get_node b4 \<union> {} \<union> {} = {} \<and> get_node b1 \<inter> get_node b3 \<union> {} = {} \<and> get_node b2 \<noteq> {} \<and> get_node b4 \<noteq> {} \<and> get_node b3 \<noteq> {}"
            by force
          then have "get_node b1 \<inter> get_node b4 \<union> {} \<union> {} = {} \<and> get_node b1 \<inter> get_node b3 \<union> {} = {} \<and> get_node b2 \<noteq> {} \<and> get_node b4 \<noteq> {} \<and> get_node b3 \<noteq> {}"
            using f3 f2 by force
          then have "(get_node b1 \<union> get_node b2) \<inter> get_node b4 \<union> {} = {} \<and> (get_node b1 \<union> get_node b2) \<inter> get_node b3 = {} \<and> get_node b4 \<noteq> {} \<and> get_node b3 \<noteq> {}"
            using f6 f5 by presburger }
        ultimately have "(get_node b1 \<union> get_node b2 \<union> get_node b3) \<inter> get_node b4 = {} \<and> (get_node b1 \<union> get_node b2) \<inter> get_node b3 = {}"
          using f4 f3 f2 f1 by (metis (no_types) Int_Un_distrib2 inf_bot_left) }
      ultimately have "(get_node b1 \<union> get_node b2 \<union> get_node b3) \<inter> get_node b4 = {} \<and> (get_node b1 \<union> get_node b2) \<inter> get_node b3 = {}"
        using f5 f3 f2 by (metis (no_types) Int_Un_distrib2 inf_bot_left inf_bot_right)
      then show ?thesis
        by (simp add: card_Un_disjoint f_node_b1 f_node_b2 f_node_b3 f_node_b4 get_node_card set_ab)
    qed 
  have node_notbelong_b1': "\<not> set (Node b1 b2 b3 b4) \<subseteq> set b1"
    using Node.prems diff_node2 by auto
  have node_notbelong_b1: "(Node b1 b2 b3 b4) \<notin> get_node b1"
    using node_notbelong_b1' get_node_set by blast
  have node_notbelong_b2': "\<not> set (Node b1 b2 b3 b4) \<subseteq> set b2"
    using Node.prems diff_node1 by auto
  have node_notbelong_b2: "(Node b1 b2 b3 b4) \<notin> get_node b2"
    using node_notbelong_b2' get_node_set by blast
  have node_notbelong_b3': "\<not> set (Node b1 b2 b3 b4) \<subseteq> set b3"
    using Node.prems diff_node1 by auto
  have node_notbelong_b3: "(Node b1 b2 b3 b4) \<notin> get_node b3"
    using node_notbelong_b3' get_node_set by blast
  have node_notbelong_b4': "\<not> set (Node b1 b2 b3 b4) \<subseteq> set b4"
    using Node.prems diff_node1 by auto
  have node_notbelong_b4: "(Node b1 b2 b3 b4) \<notin> get_node b4"
    using node_notbelong_b4' get_node_set by blast
  have card_node: "card (get_node (Node b1 b2 b3 b4)) = card (get_node b1) + card (get_node b2) + card (get_node b3) + card (get_node b4) + 1"
    using card_node_step card_node' node_notbelong_b1 node_notbelong_b2 node_notbelong_b3 node_notbelong_b4
    by (simp add: f_node_b1 f_node_b2 f_node_b3 f_node_b4)
  have card_set_node: "card (set (Node b1 b2 b3 b4)) = Suc (card (get_node (Node b1 b2 b3 b4)) * 3)"
    using card_set_step quad_b1 quad_b2 quad_b3 quad_b4 card_node by linarith
  then show ?case unfolding quadtree_def by auto
qed

subsection \<open>def and proof of inv_exact_block and inv_exact_level\<close>

type_synonym blocksize = nat

definition mapping_size_level :: "blocksize list \<Rightarrow> nat \<Rightarrow> nat"
  where "mapping_size_level bli rsize \<equiv>
        THE l. l < length bli \<and>
               rsize \<le> bli!l \<and>
               ((length bli > 1 \<and> l < (length bli - 1)) \<longrightarrow> rsize > bli!(Suc l))"

lemma le_and_eq:
  "length (bli:: blocksize list) > 1 \<Longrightarrow>
  \<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n \<Longrightarrow>
  x1 < length bli \<Longrightarrow>
  x2 < length bli \<Longrightarrow>
  x1 \<le> x2 \<Longrightarrow>
  bli!x1 \<ge> bli!x2"
proof-
  assume a0: "length (bli:: blocksize list) > 1"
     and a1: "\<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n"
     and a2: "x1 < length bli"
     and a3: "x2 < length bli"
     and a4: "x1 \<le> x2"
  {assume "x1 < x2"
    then have "bli!x1 > bli!x2" using a0 a1 a2 a3 by auto
  }moreover
  {assume "x1 = x2"
    then have "bli!x1 = bli!x2" by auto
  }
  ultimately have ?thesis using a4 by linarith 
  then show ?thesis by auto
qed

lemma middle_rsize:
  "length (bli:: blocksize list) > 1 \<Longrightarrow>
  \<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n \<Longrightarrow>
  rsize \<le> bli!0 \<Longrightarrow>
  rsize > bli!(length bli - 1) \<Longrightarrow>
  \<exists>!l. l \<ge> 0 \<and> l < length bli - 1 \<and> rsize \<le> bli!l \<and> rsize > bli!(Suc l)"
proof(induct "length bli - 1" arbitrary: bli)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have suc_xa_gr_1: "Suc xa \<ge> 1" by simp 
  {assume suc_xa_eq_1: "Suc xa = 1"
    have len_eq_2: "length bli = 2" using suc_xa_eq_1 Suc(2) by auto
    have n_eq_0: "rsize \<le> bli!0 \<and> rsize > bli!(Suc 0)"
      using Suc.hyps(2) Suc.prems(3) Suc.prems(4) suc_xa_eq_1 by auto
    then have ?case using Suc.hyps(2) suc_xa_eq_1 by auto 
  }
  moreover
  {assume suc_xa_gr_1: "Suc xa > 1"
    have xa_val: "xa = length (butlast bli) - 1" using Suc(2) nth_butlast by auto
    have butlast_gr_1: "length (butlast bli) > 1" using suc_xa_gr_1 xa_val by auto
    have bli_imp: "\<forall>m<length (butlast bli). \<forall>n<length (butlast bli). m < n \<longrightarrow> (butlast bli) ! m > (butlast bli) ! n"
      using Suc(4) by (simp add: nth_butlast) 
    have rsize_le_butlast: "rsize \<le> (butlast bli) ! 0"
      using Suc(5) by (metis Suc.hyps(2) length_butlast nth_butlast zero_less_Suc)
    {assume rsize_case0: "rsize > (butlast bli)!(length (butlast bli) - 1)"
      have step_case0: "\<exists>!l. l \<ge> 0 \<and> l < (length (butlast bli)) - 1 \<and> rsize \<le> (butlast bli)!l \<and> rsize > (butlast bli)!(Suc l)"
        using Suc(1) xa_val butlast_gr_1 bli_imp rsize_le_butlast rsize_case0 by presburger
      have last_case0: "(butlast bli)!(length (butlast bli) - 1) > bli!(length bli - 1)"
        by (metis (no_types, hide_lams) Suc.hyps(2) Suc.prems(2) diff_le_self length_butlast less_le less_trans n_not_Suc_n nth_butlast xa_val) 
      have "\<exists>!l. 0 \<le> l \<and> l < length bli - 1 \<and> rsize \<le> bli ! l \<and> rsize > bli ! Suc l"
        using step_case0 last_case0 rsize_case0
        by (metis (no_types, lifting) Suc.hyps(2) Suc_mono length_butlast less_Suc_eq not_less nth_butlast xa_val)
    }moreover
    {assume rsize_case1: "rsize \<le> (butlast bli)!(length (butlast bli) - 1)"
      have "rsize \<le> bli!((length bli - 1) - 1) \<and> rsize > bli!(length bli - 1)"
        using rsize_case1 Suc(6) by (metis Suc.hyps(2) diff_Suc_1 length_butlast lessI nth_butlast) 
      then have "\<exists>!l. 0 \<le> l \<and> l < length bli - 1 \<and> rsize \<le> bli ! l \<and> rsize > bli ! Suc l"
        using Suc(2,4) Suc.prems(1) nth_butlast butlast_gr_1 calculation
        by (smt One_nat_def Suc_lessD diff_Suc_1 diff_less_Suc length_butlast lessI less_SucE less_imp_le_nat less_trans_Suc)
    }
    ultimately have ?case by linarith
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma the_level:
  "length (bli:: blocksize list) > 0 \<Longrightarrow>
  \<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n \<Longrightarrow>
  rsize \<le> bli!0 \<Longrightarrow>
  \<exists>!l. l < length bli \<and>
       rsize \<le> bli!l \<and>
       ((length bli > 1 \<and> l < (length bli - 1)) \<longrightarrow> rsize > bli!(Suc l))"
proof(cases "length (bli:: blocksize list) > 1")
  case True
  assume a0: "length (bli:: blocksize list) > 0"
     and a1: "\<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n"
     and a2: "rsize \<le> bli!0"
  {assume b0: "rsize \<le> bli!(length bli - 1)"
    have b1: "length bli - 1 < length bli" using a0 by auto
    moreover have "rsize \<le> bli!(length bli - 1)" using b0 by auto
    moreover have "((length bli > 1 \<and> (length bli - 1) < (length bli - 1)) \<longrightarrow> rsize > bli!(Suc (length bli - 1)))" by auto
    ultimately have exist_l: "\<exists>l. l < length bli \<and>
                                  rsize \<le> bli!l \<and>
                                  ((length bli > 1 \<and> l < (length bli - 1)) \<longrightarrow> rsize > bli!(Suc l))" by auto
    then obtain l where obtain_l: "l < length bli \<and>
                                  rsize \<le> bli!l \<and>
                                  ((length bli > 1 \<and> l < (length bli - 1)) \<longrightarrow> rsize > bli!(Suc l))" by auto
    {assume "l \<ge> length bli"
      then have ?thesis using obtain_l by auto
    }
    then have s0: "\<not> l \<ge> length bli"
      using obtain_l by linarith
    moreover
    {assume b2: "l < length bli - 1"
      then have b3: "rsize > bli!(Suc l)" using True obtain_l by auto
      have "Suc l \<le> length bli - 1" using b2 by auto
      then have "bli!(Suc l) \<ge> bli!(length bli - 1)"
        using le_and_eq True a1 b1 b2 obtain_l
        by (metis Suc_lessI le_antisym less_or_eq_imp_le)
      then have "bli!(Suc l) \<ge> rsize" using b0 by auto
      then have ?thesis using b3 by auto
    }
    then have s1: "\<not> l < length bli - 1"
      using b1 b0 obtain_l by blast
    ultimately have "l = length bli - 1" using obtain_l by linarith
    then have ?thesis using obtain_l True a0 a1
      by (smt Suc_diff_1 Suc_leI less_SucE less_imp_le_nat less_trans_Suc not_less_eq_eq)
  }
  moreover
  {assume c0: "rsize > bli!(length bli - 1)"
    have c1: "\<exists>!l. l \<ge> 0 \<and> l < length bli - 1 \<and> rsize \<le> bli!l \<and> rsize > bli!(Suc l)"
      using middle_rsize True a1 a2 c0 by auto
    obtain l where middle_l: "l \<ge> 0 \<and> l < length bli - 1 \<and> rsize \<le> bli!l \<and> rsize > bli!(Suc l)"
      using c1 by auto
    then have "l < length bli \<and>
              rsize \<le> bli!l \<and>
              ((length bli > 1 \<and> l < (length bli - 1)) \<longrightarrow> rsize > bli!(Suc l))" by auto
    then have ?thesis
      by (metis (no_types, lifting) Suc_diff_1 True a0 c1 calculation le0 less_SucE) 
  }
  ultimately have ?thesis by linarith
  then show ?thesis by auto
next
  case False
  assume d0: "length bli > 0"
     and d1: "rsize \<le> bli!0"
  have "length bli = 1" using d0 False by linarith
  then show ?thesis using d0 d1 hd_conv_nth by force
qed

lemma exact_level1:
  "length (bli:: blocksize list) > 0 \<Longrightarrow>
  \<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n \<Longrightarrow>
  rsize \<le> bli!(length bli - 1) \<Longrightarrow>
  mapping_size_level bli rsize = length bli - 1"
proof-
  assume a0: "length (bli:: blocksize list) > 0"
     and a1: "\<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n"
     and a2: "rsize \<le> bli!(length bli - 1)"
  then have "bli!0 \<ge> bli!(length bli - 1)"
    by (metis One_nat_def Suc_lessI diff_less diff_self_eq_0 less_numeral_extra(1) less_or_eq_imp_le zero_less_diff)
  then have a3: "rsize \<le> bli!0" using a2 by auto
  have exist_l: "\<exists>!l. l < length bli \<and> rsize \<le> bli ! l \<and> (1 < length bli \<and> l < length bli - 1 \<longrightarrow> rsize > bli ! Suc l)"
    using the_level a0 a1 a3 by auto
  obtain l where obtain_l: "l < length bli \<and> rsize \<le> bli ! l \<and> (1 < length bli \<and> l < length bli - 1 \<longrightarrow> rsize > bli ! Suc l)"
    using exist_l by auto
  {assume len_gr_1: "length (bli:: blocksize list) > 1"
    {assume "l \<ge> length bli"
      then have ?thesis unfolding mapping_size_level_def using obtain_l by auto
    }
    then have s0: "\<not> l \<ge> length bli"
      using obtain_l by linarith
    moreover
    {assume l_le_len_sub: "l < length bli - 1"
      then have rsize_gr_suc: "rsize > bli!(Suc l)"
        using obtain_l len_gr_1 by auto
      have "Suc l \<le> length bli - 1" using l_le_len_sub by auto
      then have "bli!(Suc l) \<ge> bli!(length bli - 1)"
        using le_and_eq len_gr_1 a0 a1 a2 obtain_l exist_l
        by (metis diff_less less_numeral_extra(1) l_le_len_sub nat_neq_iff)
      then have "rsize \<le> bli!(Suc l)"
        using a2 by auto
      then have ?thesis using rsize_gr_suc by auto
    }
    then have s1: "\<not> l < length bli - 1"
      using a0 a2 obtain_l exist_l by (metis diff_less less_irrefl zero_less_one)
    ultimately have "l = length bli - 1" using obtain_l by linarith
    then have ?thesis unfolding mapping_size_level_def using obtain_l exist_l
      by (metis (no_types, lifting) the_equality) 
  }
  moreover
  {assume "\<not> (length (bli:: blocksize list) > 1)"
    then have "length bli = 1" using a0 by linarith
    then have ?thesis unfolding mapping_size_level_def
      using obtain_l a3 by force
  }
  ultimately have ?thesis by linarith
  then show ?thesis by auto
qed

lemma exact_level2:
  "length (bli:: blocksize list) > 1 \<Longrightarrow>
  \<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n \<Longrightarrow>
  l < length bli - 1 \<Longrightarrow>
  rsize \<le> bli!l \<Longrightarrow>
  rsize > bli!(Suc l) \<Longrightarrow>
  mapping_size_level bli rsize = l"
proof-
  assume a0: "length (bli:: blocksize list) > 1"
     and a1: "\<forall>m < length bli. \<forall>n < length bli. m < n \<longrightarrow> bli!m > bli!n"
     and a2: "l < length bli - 1 "
     and a3: "rsize \<le> bli!l"
     and a4: "rsize > bli!(Suc l)"
  have "l \<ge> 0" using a0 a2 by auto
  then have "bli!l \<le> bli!0"
    using le_and_eq a0 a1 a2
    by (metis (no_types, hide_lams) less_imp_diff_less neq0_conv not_less not_less_eq order.asym)
  then have rsize_le_fst: "rsize \<le> bli!0" using a3 by auto
  have rsize_gr_last: "rsize > bli!(length bli - 1)" using a2 a4
    by (smt Suc_lessD Suc_lessI a0 a1 diff_less less_numeral_extra(1) less_trans_Suc)
  have exist_n: "\<exists>!l. l \<ge> 0 \<and> l < length bli - 1 \<and> rsize \<le> bli!l \<and> rsize > bli!(Suc l)"
    using middle_rsize a0 a1 rsize_le_fst rsize_gr_last by auto
  then have ?thesis unfolding mapping_size_level_def using a0 a2 a3 a4
  proof -
    have f1: "\<And>n. \<not> length bli - 1 < n \<or> length bli \<le> n"
      by (metis (no_types) One_nat_def Suc_diff_1 Suc_leI a0 less_trans zero_less_Suc)
    have "\<forall>p n. \<exists>na. \<forall>nb. \<not> (nb::nat) < nb \<and> (na::nat) \<noteq> n \<and> (\<not> p n \<or> p na \<or> The p = n)"
      by (metis (full_types) less_not_refl n_not_Suc_n theI_unique)
    then obtain nn :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
      f2: "\<And>n p na. \<not> (n::nat) < n \<and> nn p na \<noteq> na \<and> (\<not> p na \<or> p (nn p na) \<or> The p = na)"
      by moura
    have f3: "\<not> rsize \<le> bli ! (length bli - 1)"
      using rsize_gr_last by linarith
    have "l < length bli"
      using a2 by linarith
    then show "(THE l. l < length bli \<and> rsize \<le> bli ! l \<and> (1 < length bli \<and> l < length bli - 1 \<longrightarrow> rsize > bli ! Suc l)) = l"
      using f3 f2 f1 by (metis (lifting) a0 a3 a4 exist_n le0 nat_neq_iff not_less)
  qed
  then show ?thesis by auto
qed

subsection \<open>def and proof of pre-post conditions\<close>

definition freesets_pool :: "Block set \<Rightarrow> Block set"
  where "freesets_pool bset= {l. \<exists>b \<in> bset. l \<in> freesets b}"

definition allocsets :: "Block \<Rightarrow> Block set"
  where "allocsets b = {l. leaf l \<and> L l \<in> set b \<and> fst (L l) = ALLOC}"

definition allocsets_pool :: "Block set \<Rightarrow> Block set"
  where "allocsets_pool bset= {l. \<exists>b \<in> bset. l \<in> allocsets b}"

lemma freesets_node:
  "freesets (Node b1 b2 b3 b4) = freesets b1 \<union> freesets b2 \<union> freesets b3 \<union> freesets b4"
  unfolding freesets_def by auto

lemma allocsets_node:
  "allocsets (Node b1 b2 b3 b4) = allocsets b1 \<union> allocsets b2 \<union> allocsets b3 \<union> allocsets b4"
  unfolding allocsets_def by auto

lemma alloc_fail_branch:
  "\<not> (exists_freelevel bset lv) \<Longrightarrow>
  fst (alloc bset lv ids) = bset"
  unfolding alloc_def Let_def by auto

lemma notbelong_freesets_after_replace:
  "diff_ids B \<Longrightarrow>
  leaf b \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b ALLOC \<Longrightarrow>
  b \<notin> freesets (replace B b b')"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(4) by fastforce
  have leaf_b': "b' = Leaf (ALLOC, snd x)"
    using Leaf.prems(5) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B: "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
    using leaf_b leaf_b' unfolding replace_def by auto
  have empty_freesets: "freesets (Leaf (ALLOC, snd x)) = {}"
    unfolding freesets_def by auto
  then show ?case using leaf_B by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have not_free_b1: "b \<notin> freesets (replace b1 b b')"
      using Node.hyps(1) diff_b1 Node.prems(2) Node.prems(3) a0 Node.prems(5) by auto
    have not_free_b2: "b \<notin> freesets b2"
      using no_belong_b2 unfolding freesets_def by auto
    have not_free_b3: "b \<notin> freesets b3"
      using no_belong_b3 unfolding freesets_def by auto
    have not_free_b4: "b \<notin> freesets b4"
      using no_belong_b4 unfolding freesets_def by auto
    have not_free_node: "b \<notin> freesets (Node (replace b1 b b') b2 b3 b4)"
      using not_free_b1 not_free_b2 not_free_b3 not_free_b4
      unfolding freesets_def by auto
    have ?case using replace_re not_free_node by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have not_free_b2: "b \<notin> freesets (replace b2 b b')"
      using Node.hyps(2) diff_b2 Node.prems(2) Node.prems(3) a1 Node.prems(5) by auto
    have not_free_b1: "b \<notin> freesets b1"
      using no_belong_b1 unfolding freesets_def by auto
    have not_free_b3: "b \<notin> freesets b3"
      using no_belong_b3 unfolding freesets_def by auto
    have not_free_b4: "b \<notin> freesets b4"
      using no_belong_b4 unfolding freesets_def by auto
    have not_free_node: "b \<notin> freesets (Node b1 (replace b2 b b') b3 b4)"
      using not_free_b1 not_free_b2 not_free_b3 not_free_b4
      unfolding freesets_def by auto
    have ?case using replace_re not_free_node by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have not_free_b3: "b \<notin> freesets (replace b3 b b')"
      using Node.hyps(3) diff_b3 Node.prems(2) Node.prems(3) a2 Node.prems(5) by auto
    have not_free_b1: "b \<notin> freesets b1"
      using no_belong_b1 unfolding freesets_def by auto
    have not_free_b2: "b \<notin> freesets b2"
      using no_belong_b2 unfolding freesets_def by auto
    have not_free_b4: "b \<notin> freesets b4"
      using no_belong_b4 unfolding freesets_def by auto
    have not_free_node: "b \<notin> freesets (Node b1 b2 (replace b3 b b') b4)"
      using not_free_b1 not_free_b2 not_free_b3 not_free_b4
      unfolding freesets_def by auto
    have ?case using replace_re not_free_node by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) by auto
    have not_free_b4: "b \<notin> freesets (replace b4 b b')"
      using Node.hyps(4) diff_b4 Node.prems(2) Node.prems(3) a3 Node.prems(5) by auto
    have not_free_b1: "b \<notin> freesets b1"
      using no_belong_b1 unfolding freesets_def by auto
    have not_free_b2: "b \<notin> freesets b2"
      using no_belong_b2 unfolding freesets_def by auto
    have not_free_b3: "b \<notin> freesets b3"
      using no_belong_b3 unfolding freesets_def by auto
    have not_free_node: "b \<notin> freesets (Node b1 b2 b3 (replace b4 b b'))"
      using not_free_b1 not_free_b2 not_free_b3 not_free_b4
      unfolding freesets_def by auto
    have ?case using replace_re not_free_node by auto
  }
  ultimately have ?case using Node.prems(4) by fastforce
  then show ?case by auto
qed

lemma alloc_direct_sub_freesets:
  "diff_ids B \<Longrightarrow>
  leaf b \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b ALLOC \<Longrightarrow>
  freesets B = freesets (replace B b b') \<union> {b}"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(4) by fastforce
  have value_b: "b = Leaf x"
    using Leaf.prems(2) leaf_b by auto
  have one_freesets: "freesets (Leaf x) = {Leaf x}"
    unfolding freesets_def using Leaf.prems(2,3) value_b by auto
  have leaf_b': "b' = Leaf (ALLOC, snd x)"
    using Leaf.prems(5) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B: "replace (Leaf x) b b' = Leaf (ALLOC, snd x)"
    using leaf_b leaf_b' unfolding replace_def by auto
  have empty_freesets: "freesets (Leaf (ALLOC, snd x)) = {}"
    unfolding freesets_def by auto
  show ?case using one_freesets leaf_B empty_freesets value_b by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b1: "freesets b1 = freesets (replace b1 b b') \<union> {b}"
      using Node.hyps(1) diff_b1 Node.prems(2) Node.prems(3) a0 Node.prems(5) by auto
    have ?case using replace_re sub_b1 freesets_node by simp
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b2: "freesets b2 = freesets (replace b2 b b') \<union> {b}"
      using Node.hyps(2) diff_b2 Node.prems(2) Node.prems(3) a1 Node.prems(5) by auto
    have ?case using replace_re sub_b2 freesets_node by simp
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b3: "freesets b3 = freesets (replace b3 b b') \<union> {b}"
      using Node.hyps(3) diff_b3 Node.prems(2) Node.prems(3) a2 Node.prems(5) by auto
    have ?case using replace_re sub_b3 freesets_node by simp
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) by auto
    have sub_b4: "freesets b4 = freesets (replace b4 b b') \<union> {b}"
      using Node.hyps(4) diff_b4 Node.prems(2) Node.prems(3) a3 Node.prems(5) by auto
    have ?case using replace_re sub_b4 freesets_node by simp
  }
  ultimately have ?case using Node.prems(4) by fastforce
  then show ?case by auto
qed

lemma alloc_direct_branch_freesets:
  "diff_ids_valid bset \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax = lv \<Longrightarrow>
  (newbset, newids, re, reid) = alloc1 bset lv ids \<Longrightarrow> 
  \<exists>l. l \<in> freesets_pool bset \<and> l \<notin> freesets_pool newbset \<and> freesets_pool bset = freesets_pool newbset \<union> {l}"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "exists_freelevel bset lv"
     and a2: "lmax = freesets_maxlevel bset lv"
     and a3: "lmax = lv"
     and a4: "(newbset, newids, re, reid) = alloc1 bset lv ids"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a1 by auto
  have eq_lv: "lv = (THE lmax. lmax \<le> lv \<and>
                    freesets_level_pool bset lmax \<noteq> {} \<and>
                    (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a2 a3 unfolding freesets_maxlevel_def by auto
  have the_lv: "lv \<le> lv \<and>
               freesets_level_pool bset lv \<noteq> {} \<and>
               (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lv)"
    using the_P[OF exi_lmax eq_lv] by auto
(*------------------------------------------------------------------------------------------------*)
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
    using the_lv unfolding freesets_level_pool_def by auto
  let ?blo = "SOME b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
  have the_blo: "?blo \<in> bset \<and> freesets_level ?blo lv \<noteq> {}"
    using someI_ex[OF exi_b] by auto
  have diff_blo: "diff_ids ?blo"
    using diff_bset1 exi_b
    by (metis (mono_tags, lifting) some_eq_ex) 
  have exi_l: "\<exists>l. l \<in> freesets_level ?blo lv"
    using someI_ex[OF exi_b] by auto
  let ?l = "SOME l. l \<in> freesets_level ?blo lv"
  have the_l: "?l \<in> freesets_level ?blo lv"
    using someI_ex[OF exi_l] by auto
  have leaf_freesets: "?l \<in> freesets ?blo"
    using the_l unfolding freesets_level_def by auto
  have leaf_l: "leaf ?l"
    using leaf_freesets unfolding freesets_def by simp
  have leaf_free: "fst (L ?l) = FREE"
    using leaf_freesets unfolding freesets_def by simp
  have leaf_belong: "L ?l \<in> set ?blo"
    using leaf_freesets unfolding freesets_def by simp
  have leaf_notbelong: "\<forall>b. b \<in> bset \<and> b \<noteq> ?blo \<longrightarrow> L ?l \<notin> set b"
    using diff_bset2 leaf_belong unfolding id_set_def
    by (metis (no_types, lifting) IntI emptyE image_eqI the_blo tree.set_map)
  have leaf_freesets_pool: "?l \<in> freesets_pool bset"
    using the_l the_blo unfolding freesets_level_def freesets_pool_def by auto
  have not_leaf_freesets_pool: "?l \<notin> freesets_pool (bset - {?blo})"
    using leaf_notbelong unfolding freesets_pool_def freesets_def by blast
(*------------------------------------------------------------------------------------------------*)
  let ?newb = "replace ?blo ?l (set_state_type ?l ALLOC)"
  have not_free_newblo: "?l \<notin> freesets ?newb"
    using notbelong_freesets_after_replace diff_blo leaf_l leaf_free leaf_belong by simp
  have change_freesets: "freesets ?blo = freesets ?newb \<union> {?l}"
    using alloc_direct_sub_freesets diff_blo leaf_l leaf_free leaf_belong by simp
(*------------------------------------------------------------------------------------------------*)
  have alloc1_re: "(newbset, newids, re, reid) = (((bset - {?blo}) \<union> {?newb}), ids, True, {snd (L ?l)})"
    using a4 unfolding alloc1_def by metis
  have leaf_not_freesets_pool: "?l \<notin> freesets_pool newbset"
    using alloc1_re not_leaf_freesets_pool not_free_newblo unfolding freesets_pool_def by blast
  have step1: "freesets_pool bset = freesets_pool (bset - {?blo}) \<union> freesets ?blo"
    unfolding freesets_pool_def using the_blo by auto
  have step2: "freesets_pool newbset = freesets_pool (bset - {?blo}) \<union> freesets ?newb"
    unfolding freesets_pool_def using alloc1_re by auto
  have change_freesets_pool: "freesets_pool bset = freesets_pool newbset \<union> {?l}"
    using step1 step2 change_freesets by auto
  show ?thesis using leaf_freesets_pool leaf_not_freesets_pool change_freesets_pool by auto
qed

lemma notbelong_allocsets_before_replace:
  "diff_ids B \<Longrightarrow>
  leaf b \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b ALLOC \<Longrightarrow>
  b' \<notin> allocsets B"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(4) by fastforce
  have free_b: "fst x = FREE"
    using Leaf.prems(3) leaf_b by auto
  have empty_allocsets: "allocsets (Leaf x) = {}"
    unfolding allocsets_def using free_b by auto
  have leaf_b': "b' = Leaf (ALLOC, snd x)"
    using Leaf.prems(5) leaf_b unfolding set_state_type_def Let_def by auto
  show ?case using empty_allocsets by auto
next
  case (Node b1 b2 b3 b4)
  have same_id: "snd (L b') = snd (L b)"
    using Node.prems(5) unfolding set_state_type_def Let_def by auto
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have not_allocsets_b1: "b' \<notin> allocsets b1"
      using Node.hyps(1) diff_b1 Node.prems(2) Node.prems(3) a0 Node.prems(5) by auto
    have not_set_b2: "L b' \<notin> set b2"
      using a0 diff_ab same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b2: "b' \<notin> allocsets b2"
      using not_set_b2 unfolding allocsets_def by auto
    have not_set_b3: "L b' \<notin> set b3"
      using a0 diff_ac same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b3: "b' \<notin> allocsets b3"
      using not_set_b3 unfolding allocsets_def by auto
    have not_set_b4: "L b' \<notin> set b4"
      using a0 diff_ad same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b4: "b' \<notin> allocsets b4"
      using not_set_b4 unfolding allocsets_def by auto
    have not_free_node: "b' \<notin> allocsets (Node b1 b2 b3 b4)"
      using not_allocsets_b1 not_allocsets_b2 not_allocsets_b3 not_allocsets_b4
      unfolding allocsets_def using allocsets_node by auto
    have ?case using not_free_node by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have not_allocsets_b2: "b' \<notin> allocsets b2"
      using Node.hyps(2) diff_b2 Node.prems(2) Node.prems(3) a1 Node.prems(5) by auto
    have not_set_b1: "L b' \<notin> set b1"
      using a1 diff_ab same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b1: "b' \<notin> allocsets b1"
      using not_set_b1 unfolding allocsets_def by auto
    have not_set_b3: "L b' \<notin> set b3"
      using a1 diff_bc same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b3: "b' \<notin> allocsets b3"
      using not_set_b3 unfolding allocsets_def by auto
    have not_set_b4: "L b' \<notin> set b4"
      using a1 diff_bd same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b4: "b' \<notin> allocsets b4"
      using not_set_b4 unfolding allocsets_def by auto
    have not_free_node: "b' \<notin> allocsets (Node b1 b2 b3 b4)"
      using not_allocsets_b1 not_allocsets_b2 not_allocsets_b3 not_allocsets_b4
      unfolding allocsets_def using allocsets_node by auto
    have ?case using not_free_node by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have not_allocsets_b3: "b' \<notin> allocsets b3"
      using Node.hyps(3) diff_b3 Node.prems(2) Node.prems(3) a2 Node.prems(5) by auto
    have not_set_b1: "L b' \<notin> set b1"
      using a2 diff_ac same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b1: "b' \<notin> allocsets b1"
      using not_set_b1 unfolding allocsets_def by auto
    have not_set_b2: "L b' \<notin> set b2"
      using a2 diff_bc same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b2: "b' \<notin> allocsets b2"
      using not_set_b2 unfolding allocsets_def by auto
    have not_set_b4: "L b' \<notin> set b4"
      using a2 diff_cd same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b4: "b' \<notin> allocsets b4"
      using not_set_b4 unfolding allocsets_def by auto
    have not_free_node: "b' \<notin> allocsets (Node b1 b2 b3 b4)"
      using not_allocsets_b1 not_allocsets_b2 not_allocsets_b3 not_allocsets_b4
      unfolding allocsets_def using allocsets_node by auto
    have ?case using not_free_node by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have not_allocsets_b4: "b' \<notin> allocsets b4"
      using Node.hyps(4) diff_b4 Node.prems(2) Node.prems(3) a3 Node.prems(5) by auto
    have not_set_b1: "L b' \<notin> set b1"
      using a3 diff_ad same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b1: "b' \<notin> allocsets b1"
      using not_set_b1 unfolding allocsets_def by auto
    have not_set_b2: "L b' \<notin> set b2"
      using a3 diff_bd same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b2: "b' \<notin> allocsets b2"
      using not_set_b2 unfolding allocsets_def by auto
    have not_set_b3: "L b' \<notin> set b3"
      using a3 diff_cd same_id unfolding id_set_def
      by (metis IntI emptyE image_eqI tree.set_map)
    have not_allocsets_b3: "b' \<notin> allocsets b3"
      using not_set_b3 unfolding allocsets_def by auto
    have not_free_node: "b' \<notin> allocsets (Node b1 b2 b3 b4)"
      using not_allocsets_b1 not_allocsets_b2 not_allocsets_b3 not_allocsets_b4
      unfolding allocsets_def using allocsets_node by auto
    have ?case using not_free_node by auto
  }
  ultimately have ?case using Node.prems(4) by fastforce
  then show ?case by auto
qed

lemma alloc_direct_sub_allocsets:
  "diff_ids B \<Longrightarrow>
  leaf b \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b ALLOC \<Longrightarrow>
  allocsets (replace B b b') = allocsets B \<union> {b'}"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(4) by fastforce
  have free_b: "fst x = FREE"
    using Leaf.prems(3) leaf_b by auto
  have empty_allocsets: "allocsets (Leaf x) = {}"
    unfolding allocsets_def using free_b by auto
  have leaf_b': "b' = Leaf (ALLOC, snd x)"
    using Leaf.prems(5) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B: "replace (Leaf x) b b' = b'"
    using leaf_b leaf_b' unfolding replace_def by auto
  have b1: "leaf b'"
    using leaf_b' by simp
  have b2: "L b' \<in> tree.set b'"
    using leaf_b' by auto
  have b3: "fst (L b') = ALLOC"
    using leaf_b' by simp 
  have one_allocsets: "allocsets b' = {b'}"
    unfolding allocsets_def using b1 b2 b3 apply auto
    by (metis singletonD tree.collapse(1) tree.simps(15))
  show ?case using leaf_B one_allocsets empty_allocsets by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b1: "allocsets (replace b1 b b') = allocsets b1 \<union> {b'}"
      using Node.hyps(1) diff_b1 Node.prems(2) Node.prems(3) a0 Node.prems(5) by auto
    have ?case using replace_re sub_b1 allocsets_node by simp
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b2: "allocsets (replace b2 b b') = allocsets b2 \<union> {b'}"
      using Node.hyps(2) diff_b2 Node.prems(2) Node.prems(3) a1 Node.prems(5) by auto
    have ?case using replace_re sub_b2 allocsets_node by simp
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
   have sub_b3: "allocsets (replace b3 b b') = allocsets b3 \<union> {b'}"
      using Node.hyps(3) diff_b3 Node.prems(2) Node.prems(3) a2 Node.prems(5) by auto
    have ?case using replace_re sub_b3 allocsets_node by simp
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) by auto
    have sub_b4: "allocsets (replace b4 b b') = allocsets b4 \<union> {b'}"
      using Node.hyps(4) diff_b4 Node.prems(2) Node.prems(3) a3 Node.prems(5) by auto
    have ?case using replace_re sub_b4 allocsets_node by simp
  }
  ultimately have ?case using Node.prems(4) by fastforce
  then show ?case by auto
qed

lemma alloc_direct_branch_allocsets:
  "diff_ids_valid bset \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax = lv \<Longrightarrow>
  (newbset, newids, re, reid) = alloc1 bset lv ids \<Longrightarrow>
  \<exists>l. l \<notin> allocsets_pool bset \<and> l \<in> allocsets_pool newbset \<and> allocsets_pool newbset = allocsets_pool bset \<union> {l}"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "exists_freelevel bset lv"
     and a2: "lmax = freesets_maxlevel bset lv"
     and a3: "lmax = lv"
     and a4: "(newbset, newids, re, reid) = alloc1 bset lv ids"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a1 by auto
  have eq_lv: "lv = (THE lmax. lmax \<le> lv \<and>
                    freesets_level_pool bset lmax \<noteq> {} \<and>
                    (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a2 a3 unfolding freesets_maxlevel_def by auto
  have the_lv: "lv \<le> lv \<and>
               freesets_level_pool bset lv \<noteq> {} \<and>
               (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lv)"
    using the_P[OF exi_lmax eq_lv] by auto
(*------------------------------------------------------------------------------------------------*)
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
    using the_lv unfolding freesets_level_pool_def by auto
  let ?blo = "SOME b. b \<in> bset \<and> freesets_level b lv \<noteq> {}"
  have the_blo: "?blo \<in> bset \<and> freesets_level ?blo lv \<noteq> {}"
    using someI_ex[OF exi_b] by auto
  have diff_blo: "diff_ids ?blo"
    using diff_bset1 exi_b
    by (metis (mono_tags, lifting) some_eq_ex) 
  have exi_l: "\<exists>l. l \<in> freesets_level ?blo lv"
    using someI_ex[OF exi_b] by auto
  let ?l = "SOME l. l \<in> freesets_level ?blo lv"
  have the_l: "?l \<in> freesets_level ?blo lv"
    using someI_ex[OF exi_l] by auto
  have leaf_freesets: "?l \<in> freesets ?blo"
    using the_l unfolding freesets_level_def by auto
  have leaf_l: "leaf ?l"
    using leaf_freesets unfolding freesets_def by simp
  have leaf_free: "fst (L ?l) = FREE"
    using leaf_freesets unfolding freesets_def by simp
  have leaf_belong: "L ?l \<in> set ?blo"
    using leaf_freesets unfolding freesets_def by simp
(*------------------------------------------------------------------------------------------------*)
  let ?l' = "set_state_type ?l ALLOC"
  have leaf_notbelong: "?l' \<notin> allocsets ?blo"
    using notbelong_allocsets_before_replace diff_blo leaf_l leaf_free leaf_belong by simp
  have same_id: "snd (L ?l') = snd (L ?l)"
    unfolding set_state_type_def Let_def by auto
  have leaf_notbelong_ids': "\<forall>b. b \<in> bset \<and> b \<noteq> ?blo \<longrightarrow> snd (L ?l) \<notin> id_set b"
    using diff_bset2 leaf_belong unfolding id_set_def
    by (metis (no_types, lifting) IntI emptyE image_eqI the_blo tree.set_map)
  have leaf_notbelong_ids: "\<forall>b. b \<in> bset \<and> b \<noteq> ?blo \<longrightarrow> snd (L ?l') \<notin> id_set b"
    using leaf_notbelong_ids' same_id by auto
  have leaf_notbelong_set: "\<forall>b. b \<in> bset \<and> b \<noteq> ?blo \<longrightarrow> L ?l' \<notin> set b"
    using leaf_notbelong_ids unfolding id_set_def
    using tree.set_map by fastforce
  have leat_notbelong_allocsets: "?l' \<notin> allocsets_pool bset"
    using leaf_notbelong leaf_notbelong_set unfolding allocsets_pool_def allocsets_def by blast
  let ?newb = "replace ?blo ?l ?l'"
  have change_allocsets: "allocsets ?newb = allocsets ?blo \<union> {?l'}"
    using alloc_direct_sub_allocsets diff_blo leaf_l leaf_free leaf_belong by simp
  have leaf_allocsets: "?l' \<in> allocsets ?newb"
    using change_allocsets by auto
(*------------------------------------------------------------------------------------------------*)
  have alloc1_re: "(newbset, newids, re, reid) = (((bset - {?blo}) \<union> {?newb}), ids, True, {snd (L ?l)})"
    using a4 unfolding alloc1_def by metis
  have leaf_allocsets_pool: "?l' \<in> allocsets_pool newbset"
    using alloc1_re leaf_allocsets unfolding allocsets_pool_def by blast
  have step1: "allocsets_pool bset = allocsets_pool (bset - {?blo}) \<union> allocsets ?blo"
    unfolding allocsets_pool_def using the_blo by auto
  have step2: "allocsets_pool newbset = allocsets_pool (bset - {?blo}) \<union> allocsets ?newb"
    unfolding allocsets_pool_def using alloc1_re by auto
  have change_allocsets_pool: "allocsets_pool newbset = allocsets_pool bset \<union> {?l'}"
    using step1 step2 change_allocsets by auto
  show ?thesis using leat_notbelong_allocsets leaf_allocsets_pool change_allocsets_pool by auto
qed

lemma allocated_leaf_after_split:
  "lmax < lv \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (L b) \<in> ids \<Longrightarrow>
  \<exists>!l. leaf l \<and> allocsets (fst (split b ids (lv - lmax))) = {l}"
proof(induct "lv - lmax" arbitrary: lmax b ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide b ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and pll_alloc: "fst ll = ALLOC" and pll_leaf: "leaf (Leaf ll)"
      and plr_free: "fst lr = FREE" and plr_leaf: "leaf (Leaf lr)"
      and prl_free: "fst rl = FREE" and prl_leaf: "leaf (Leaf rl)"
      and prr_free: "fst rr = FREE" and prr_leaf: "leaf (Leaf rr)"
    unfolding divide_def Let_def by auto
  have allocsets_lr: "allocsets (Leaf lr) = {}"
    unfolding allocsets_def using plr_leaf plr_free by auto
  have allocsets_rl: "allocsets (Leaf rl) = {}"
    unfolding allocsets_def using prl_leaf prl_free by auto
  have allocsets_rr: "allocsets (Leaf rr) = {}"
    unfolding allocsets_def using prr_leaf prr_free by auto
  let ?newids = "snd (divide b ids)"
  have belong_ll: "snd ll \<in> ?newids"
    using divide_belong pdivide by auto
  have step': "fst (split b ids (lv - lmax)) = Node (fst (split (Leaf ll) ?newids (lv - lmax - 1))) (Leaf lr) (Leaf rl) (Leaf rr)"
    using split_induct Suc(3) pdivide by (meson zero_less_diff)
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_lmax: "lv = Suc lmax"
      using Suc(2) xa_eq_1 by linarith
    have lv_sub_lmax: "lv - lmax = Suc 0"
      using lv_suc_lmax by auto
    have split_ll: "fst (split (Leaf ll) ?newids (lv - lmax - 1)) = Leaf ll"
      using lv_suc_lmax by auto
    have step1: "fst (split b ids (lv - lmax)) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      using step' split_ll by auto
    have allocsets_ll: "allocsets (Leaf ll) = {Leaf ll}"
      unfolding allocsets_def using pll_leaf pll_alloc by auto
    have ?case using step1 allocsets_ll allocsets_lr allocsets_rl allocsets_rr allocsets_node by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_lmax: "xa = lv - Suc lmax"
      using Suc(2) by linarith
    have suc_lmax_less_lv: "Suc lmax < lv"
      using Suc(3) xa_gr_1 xa_lv_suc_lmax by linarith
    have step2: "fst (split b ids (lv - lmax)) = Node (fst (split (Leaf ll) ?newids (lv - Suc lmax))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using step' by auto
    have allocsets_ll: "\<exists>!l. leaf l \<and> allocsets (fst (split (Leaf ll) ?newids (lv - Suc lmax))) = {l}"
      using Suc(1) xa_lv_suc_lmax suc_lmax_less_lv divide_finite Suc(4) belong_ll pdivide by auto
    have ?case using step2 allocsets_ll allocsets_lr allocsets_rl allocsets_rr allocsets_node by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma allocsets_after_replace_leaf:
  "diff_ids blo \<Longrightarrow>
  leaf b \<Longrightarrow>
  L b \<in> tree.set blo \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  allocsets (replace_leaf blo b subbtr) = allocsets blo \<union> allocsets subbtr"
proof(induct blo)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(3) by fastforce
  have value_b: "b = Leaf x"
    using Leaf.prems(2) leaf_b by auto
  have empty_allocsets: "allocsets (Leaf x) = {}"
    unfolding allocsets_def using value_b Leaf.prems(4) by auto
  have replace_leaf_step: "replace_leaf (Leaf x) b subbtr = subbtr"
    using leaf_b replace_leaf.simps(1) by auto
  show ?case using replace_leaf_step empty_allocsets by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b2: "{snd (L b)} \<inter> id_set b2 = {}"
      using no_belong_b2 unfolding id_set_def
      using a0 diff_ab id_set_def tree.set_map by fastforce 
    have b_empty_b3: "{snd (L b)} \<inter> id_set b3 = {}"
      using no_belong_b3 unfolding id_set_def
      using a0 diff_ac id_set_def tree.set_map by fastforce 
    have b_empty_b4: "{snd (L b)} \<inter> id_set b4 = {}"
      using no_belong_b4 unfolding id_set_def
      using a0 diff_ad id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node (replace_leaf b1 b subbtr) b2 b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b2 no_belong_b3 no_belong_b4 by auto
    have step: "allocsets (replace_leaf b1 b subbtr) = allocsets b1 \<union> allocsets subbtr"
      using Node.hyps(1) diff_b1 Node.prems(2) a0 Node.prems(4) by auto
    have ?case using replace_leaf_step step allocsets_node by auto
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b1: "{snd (L b)} \<inter> id_set b1 = {}"
      using no_belong_b1 unfolding id_set_def
      using a1 diff_ab id_set_def tree.set_map by fastforce 
    have b_empty_b3: "{snd (L b)} \<inter> id_set b3 = {}"
      using no_belong_b3 unfolding id_set_def
      using a1 diff_bc id_set_def tree.set_map by fastforce 
    have b_empty_b4: "{snd (L b)} \<inter> id_set b4 = {}"
      using no_belong_b4 unfolding id_set_def
      using a1 diff_bd id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node b1 (replace_leaf b2 b subbtr) b3 b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b3 no_belong_b4 by auto
    have step: "allocsets (replace_leaf b2 b subbtr) = allocsets b2 \<union> allocsets subbtr"
      using Node.hyps(2) diff_b2 Node.prems(2) a1 Node.prems(4) by auto
    have ?case using replace_leaf_step step allocsets_node by auto
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b1: "{snd (L b)} \<inter> id_set b1 = {}"
      using no_belong_b1 unfolding id_set_def
      using a2 diff_ac id_set_def tree.set_map by fastforce 
    have b_empty_b2: "{snd (L b)} \<inter> id_set b2 = {}"
      using no_belong_b2 unfolding id_set_def
      using a2 diff_bc id_set_def tree.set_map by fastforce 
    have b_empty_b4: "{snd (L b)} \<inter> id_set b4 = {}"
      using no_belong_b4 unfolding id_set_def
      using a2 diff_cd id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node b1 b2 (replace_leaf b3 b subbtr) b4"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b4 by auto
    have step: "allocsets (replace_leaf b3 b subbtr) = allocsets b3 \<union> allocsets subbtr"
      using Node.hyps(3) diff_b3 Node.prems(2) a2 Node.prems(4) by auto
    have ?case using replace_leaf_step step allocsets_node by auto
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have b_empty_b1: "{snd (L b)} \<inter> id_set b1 = {}"
      using no_belong_b1 unfolding id_set_def
      using a3 diff_ad id_set_def tree.set_map by fastforce 
    have b_empty_b2: "{snd (L b)} \<inter> id_set b2 = {}"
      using no_belong_b2 unfolding id_set_def
      using a3 diff_bd id_set_def tree.set_map by fastforce 
    have b_empty_b3: "{snd (L b)} \<inter> id_set b3 = {}"
      using no_belong_b3 unfolding id_set_def
      using a3 diff_cd id_set_def tree.set_map by fastforce 
    have replace_leaf_step: "replace_leaf (Node b1 b2 b3 b4) b subbtr =
                            Node b1 b2 b3 (replace_leaf b4 b subbtr)"
      using replace_leaf.simps(2) no_replace_leaf no_belong_b1 no_belong_b2 no_belong_b3 by auto
    have step: "allocsets (replace_leaf b4 b subbtr) = allocsets b4 \<union> allocsets subbtr"
      using Node.hyps(4) diff_b4 Node.prems(2) a3 Node.prems(4) by auto
    have ?case using replace_leaf_step step allocsets_node by auto
  }
  ultimately have ?case using Node.prems(3) by auto 
  then show ?case by auto
qed

lemma alloc_split_branch_allocsets:
  "diff_ids_valid bset \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<forall>b\<in>bset. id_set b \<subseteq> ids \<Longrightarrow>
  exists_freelevel bset lv \<Longrightarrow>
  lmax = freesets_maxlevel bset lv \<Longrightarrow>
  lmax \<noteq> lv \<Longrightarrow>
  blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {}) \<Longrightarrow>
  b = (SOME l. l \<in> freesets_level blo lmax) \<Longrightarrow>
  (subbtr, ids') = split b ids (lv - lmax) \<Longrightarrow>
  newblo = replace_leaf blo b subbtr \<Longrightarrow>
  newbset = bset - {blo} \<union> {newblo} \<Longrightarrow>
  \<exists>l. l \<notin> allocsets_pool bset \<and> l \<in> allocsets_pool newbset \<and> allocsets_pool newbset = allocsets_pool bset \<union> {l}"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "finite ids"
     and a2: "\<forall>b\<in>bset. id_set b \<subseteq> ids"
     and a3: "exists_freelevel bset lv"
     and a4: "lmax = freesets_maxlevel bset lv"
     and a5: "lmax \<noteq> lv"
     and a6: "blo = (SOME b. b \<in> bset \<and> freesets_level b lmax \<noteq> {})"
     and a7: "b = (SOME l. l \<in> freesets_level blo lmax)"
     and a8: "(subbtr, ids') = split b ids (lv - lmax)"
     and a9: "newblo = replace_leaf blo b subbtr"
     and a10: "newbset = bset - {blo} \<union> {newblo}"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_lmax: "\<exists>!lmax. lmax \<le> lv \<and>
                  freesets_level_pool bset lmax \<noteq> {} \<and>
                  (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using exist_lmax a3 by auto
  have eq_lmax: "lmax = (THE lmax. lmax \<le> lv \<and>
                        freesets_level_pool bset lmax \<noteq> {} \<and>
                        (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax))"
    using a4 unfolding freesets_maxlevel_def by auto
  have the_lmax: "lmax < lv \<and>
                 freesets_level_pool bset lmax \<noteq> {} \<and>
                 (\<forall>l. l \<le> lv \<and> freesets_level_pool bset l \<noteq> {} \<longrightarrow> l \<le> lmax)"
    using the_P[OF exi_lmax eq_lmax] a5 by auto
  have lmax_le_lv: "lmax < lv" using the_lmax by auto
  have value_lmax: "lmax \<ge> 0" by simp
  have value_lv: "lv > 0" using the_lmax by auto
  have lmax_le_lv: "lmax < lv" using the_lmax by auto
(*------------------------------------------------------------------------------------------------*)
  have exi_b: "\<exists>b. b \<in> bset \<and> freesets_level b lmax \<noteq> {}"
    using the_lmax unfolding freesets_level_pool_def by auto
  have exi_blo: "blo \<in> bset \<and> freesets_level blo lmax \<noteq> {}"
    using someI_ex[OF exi_b] a6 by auto
  have diff_blo: "diff_ids blo"
    using diff_bset1 exi_blo by auto
  have ids_blo: "id_set blo \<subseteq> ids"
    using a2 exi_blo by auto
  have exi_l: "\<exists>l. l \<in> freesets_level blo lmax"
    using exi_blo by auto
  have exi_b: "b \<in> freesets_level blo lmax"
    using someI_ex[OF exi_l] a7 by auto
  have leaf_b: "leaf b"
    using exi_b unfolding freesets_level_def freesets_def by auto
  have b_belong_blo: "L b \<in> tree.set blo"
    using exi_b unfolding freesets_level_def freesets_def by auto
  have free_b: "fst (L b) = FREE"
    using exi_b unfolding freesets_level_def freesets_def by auto
  have ids_b: "snd (L b) \<in> ids"
    using exi_b unfolding freesets_level_def freesets_def
    using ids_blo unfolding id_set_def using tree.set_map by fastforce
(*------------------------------------------------------------------------------------------------*)
  have exi_allocated_leaf: "\<exists>!l. leaf l \<and> allocsets subbtr = {l}"
    using allocated_leaf_after_split lmax_le_lv a1 ids_b a8 fst_conv by metis
  obtain le where allocated_leaf: "leaf le \<and> allocsets subbtr = {le}"
    using exi_allocated_leaf by auto
  have allocsets_newblo': "allocsets newblo = allocsets blo \<union> allocsets subbtr"
    using allocsets_after_replace_leaf diff_blo leaf_b b_belong_blo free_b a9 by auto
  have allocsets_newblo: "allocsets newblo = allocsets blo \<union> {le}"
    using allocsets_newblo' allocated_leaf by auto
  have le_treeset_subbtr: "L le \<in> tree.set subbtr"
    using allocated_leaf unfolding allocsets_def by auto
  have le_alloc: "fst (L le) = ALLOC"
    using allocated_leaf unfolding allocsets_def by auto
  have le_allocsets_newblo: "le \<in> allocsets newblo"
    using replace_leaf_belong b_belong_blo le_treeset_subbtr a9
    unfolding allocsets_def using le_alloc allocated_leaf by simp
  have ids_subbtr: "id_set subbtr \<inter> ids = {}"
    using ids_split lmax_le_lv a1 ids_b a8 fst_conv by metis
  have leaf_notbelong_ids: "\<forall>b. b \<in> bset \<longrightarrow> snd (L le) \<notin> id_set b"
    using a2 ids_subbtr le_treeset_subbtr unfolding id_set_def
    using tree.set_map by fastforce
  have leaf_notbelong_set: "\<forall>b. b \<in> bset \<longrightarrow> L le \<notin> set b"
    using leaf_notbelong_ids unfolding id_set_def
    using tree.set_map by fastforce
  have le_allocsets_pool: "le \<notin> allocsets_pool bset"
    using leaf_notbelong_set unfolding allocsets_pool_def allocsets_def by blast
  have step1: "allocsets_pool bset = allocsets_pool (bset - {blo}) \<union> allocsets blo"
    unfolding allocsets_pool_def using exi_blo by auto
  have step2: "allocsets_pool newbset = allocsets_pool (bset - {blo}) \<union> allocsets newblo"
    unfolding allocsets_pool_def using a10 by auto
  have con1: "allocsets_pool newbset = allocsets_pool bset \<union> {le}"
    using step1 step2 allocsets_newblo by auto
  have con2: "le \<in> allocsets_pool newbset"
    using le_allocsets_newblo step2 unfolding allocsets_pool_def by auto
  show ?thesis using con1 con2 le_allocsets_pool by auto
qed

lemma free_fail_branch1:
  "\<not> (\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)) \<Longrightarrow>
  fst (free bset b lv ids) = bset"
  unfolding free_def Let_def by auto

lemma free_fail_branch2:
  "\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b) \<Longrightarrow>
  fst (L b) = FREE \<Longrightarrow>
  fst (free bset b lv ids) = bset"
  unfolding free_def Let_def by auto

lemma free_success_sub_allocsets:
  "diff_ids B \<Longrightarrow>
  leaf b \<Longrightarrow>
  fst (L b) = ALLOC \<Longrightarrow>
  L b \<in> set B \<Longrightarrow>
  b' = set_state_type b FREE \<Longrightarrow>
  allocsets B = allocsets (replace B b b') \<union> {b}"
proof(induct B)
  case (Leaf x)
  have leaf_b: "L b = x"
    using Leaf.prems(4) by fastforce
  have value_b: "b = Leaf x"
    using Leaf.prems(2) leaf_b by auto
  have one_allocsets: "allocsets (Leaf x) = {Leaf x}"
    unfolding allocsets_def using Leaf.prems(2,3) value_b by auto
  have leaf_b': "b' = Leaf (FREE, snd x)"
    using Leaf.prems(5) leaf_b unfolding set_state_type_def Let_def by auto
  have leaf_B': "replace (Leaf x) b b' = Leaf (FREE, snd x)"
    using leaf_b leaf_b' unfolding replace_def by auto
  have empty_allocsets: "allocsets (Leaf (FREE, snd x)) = {}"
    unfolding allocsets_def by auto
  show ?case using one_allocsets leaf_B' empty_allocsets value_b by auto
next
  case (Node b1 b2 b3 b4)
  have diff_b1: "diff_ids b1"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ab: "(id_set b1) \<inter> (id_set b2) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "(id_set b1) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "(id_set b1) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "(id_set b2) \<inter> (id_set b3) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "(id_set b2) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "(id_set b3) \<inter> (id_set b4) = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume a0: "L b \<in> set b1"
    have no_belong_b2: "L b \<notin> set b2"
      using a0 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a0 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a0 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node (replace b1 b b') b2 b3 b4"
      using a0 unfolding replace_def apply auto
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b1: "allocsets b1 = allocsets (replace b1 b b') \<union> {b}"
      using Node.hyps(1) diff_b1 Node.prems(2) Node.prems(3) a0 Node.prems(5) by auto
    have ?case using replace_re sub_b1 allocsets_node by simp
  }
  moreover
  {assume a1: "L b \<in> set b2"
    have no_belong_b1: "L b \<notin> set b1"
      using a1 diff_ab unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a1 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a1 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 (replace b2 b b') b3 b4"
      using a1 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b2: "allocsets b2 = allocsets (replace b2 b b') \<union> {b}"
      using Node.hyps(2) diff_b2 Node.prems(2) Node.prems(3) a1 Node.prems(5) by auto
    have ?case using replace_re sub_b2 allocsets_node by simp
  }
  moreover
  {assume a2: "L b \<in> set b3"
    have no_belong_b1: "L b \<notin> set b1"
      using a2 diff_ac unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a2 diff_bc unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b4: "L b \<notin> set b4"
      using a2 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 (replace b3 b b') b4"
      using a2 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b4 Node.prems(5) by auto
    have sub_b3: "allocsets b3 = allocsets (replace b3 b b') \<union> {b}"
      using Node.hyps(3) diff_b3 Node.prems(2) Node.prems(3) a2 Node.prems(5) by auto
    have ?case using replace_re sub_b3 allocsets_node by simp
  }
  moreover
  {assume a3: "L b \<in> set b4"
    have no_belong_b1: "L b \<notin> set b1"
      using a3 diff_ad unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b2: "L b \<notin> set b2"
      using a3 diff_bd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have no_belong_b3: "L b \<notin> set b3"
      using a3 diff_cd unfolding id_set_def
      by (metis disjoint_iff_not_equal image_eqI tree.set_map)
    have replace_re: "replace (Node b1 b2 b3 b4) b b' = Node b1 b2 b3 (replace b4 b b')"
      using a3 unfolding replace_def apply auto
      using no_replace no_belong_b1 Node.prems(5) apply auto[1]
      using no_replace no_belong_b2 Node.prems(5) apply auto[1]
      using no_replace no_belong_b3 Node.prems(5) by auto
    have sub_b4: "allocsets b4 = allocsets (replace b4 b b') \<union> {b}"
      using Node.hyps(4) diff_b4 Node.prems(2) Node.prems(3) a3 Node.prems(5) by auto
    have ?case using replace_re sub_b4 allocsets_node by simp
  }
  ultimately have ?case using Node.prems(4) by fastforce
  then show ?case by auto
qed

lemma free_success_same_allocsets:
  "allocsets (fst (merge B ids)) = allocsets B"
proof(induct B arbitrary: ids)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  {assume a0: "\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))"
    have empty_allocsets: "allocsets (Node b1 b2 b3 b4) = {}"
      using a0 unfolding allocsets_def by auto
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node b1 b2 b3 b4) ids"
      using merge.simps(2) a0 by auto
    obtain newid where com: "fst (combine (Node b1 b2 b3 b4) ids) = Leaf (FREE, newid)"
      unfolding combine_def Let_def using fst_conv a0 by auto
    have still_empty_allocsets: "allocsets (Leaf (FREE, newid)) = {}"
      unfolding allocsets_def by auto
    have ?case using empty_allocsets step com still_empty_allocsets by simp
  }
  moreover
  {assume a1: "\<not> (\<exists>xa xb xc xd. (Node b1 b2 b3 b4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd)))"
    let ?m1 = "merge b1 ids"
    have allocsets_m1: "allocsets (fst (merge b1 ids)) = allocsets b1"
      using Node.hyps(1) by auto
    let ?m2 = "merge b2 (snd ?m1)"
    have allocsets_m2: "allocsets (fst (merge b2 (snd ?m1))) = allocsets b2"
      using Node.hyps(2) by auto
    let ?m3 = "merge b3 (snd ?m2)"
    have allocsets_m3: "allocsets (fst (merge b3 (snd ?m2))) = allocsets b3"
      using Node.hyps(3) by auto
    let ?m4 = "merge b4 (snd ?m3)"
    have allocsets_m4: "allocsets (fst (merge b4 (snd ?m3))) = allocsets b4"
      using Node.hyps(4) by auto
    have step: "merge (Node b1 b2 b3 b4) ids =
                combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)"
      using merge.simps(2) a1 by meson
    have allocsets_com: "allocsets (fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4))) =
                        allocsets (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4))"
      proof(cases "\<exists>xa xb xc xd. Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4) = Node (Leaf (FREE, xa)) (Leaf (FREE, xb)) (Leaf (FREE, xc)) (Leaf (FREE, xd))")
        case True
        have empty_allocsets: "allocsets (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) = {}"
          using True unfolding allocsets_def by auto
        obtain newid where step1: "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Leaf (FREE, newid)"
          unfolding combine_def Let_def using True by auto
        have still_empty_allocsets: "allocsets (Leaf (FREE, newid)) = {}"
          unfolding allocsets_def by auto
        show ?thesis by (simp add: empty_allocsets step1 still_empty_allocsets) 
      next
        case False
        have step2: "fst (combine (Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)) (snd ?m4)) = Node (fst ?m1) (fst ?m2) (fst ?m3) (fst ?m4)"
          unfolding combine_def using False by auto
        show ?thesis by (simp add: step2) 
      qed
    have ?case using step allocsets_com
      by (simp add: allocsets_m1 allocsets_m2 allocsets_m3 allocsets_m4 allocsets_node) 
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma free_success_branch_allocsets:
  "diff_ids_valid bset \<Longrightarrow>
  leaf b \<Longrightarrow>
  \<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b) \<Longrightarrow>
  fst (L b) \<noteq> FREE \<Longrightarrow>
  (newbset, newids, re) = free bset b lv ids \<Longrightarrow>
  allocsets_pool bset = allocsets_pool newbset \<union> {b}"
proof-
  assume a0: "diff_ids_valid bset"
     and a1: "leaf b"
     and a2: "\<exists>btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)"
     and a3: "fst (L b) \<noteq> FREE"
     and a4: "(newbset, newids, re) = free bset b lv ids"
  have diff_bset1: "(\<forall>b \<in> bset. diff_ids b)"
    using a0 diff_ids_valid_def by auto
  have diff_bset2: "(\<forall>b1 b2. b1 \<in> bset \<and> b2 \<in> bset \<and> b1 \<noteq> b2 \<longrightarrow> id_set b1 \<inter> id_set b2 = {})"
    using a0 diff_ids_valid_def by auto
  have exi_btree: "\<exists>!btree \<in> bset. (L b) \<in> set btree \<and> lv = get_level btree (L b)"
    using a3 diff_bset2
    proof -
      { fix tt :: "(block_state_type \<times> nat) tree" and tta :: "(block_state_type \<times> nat) tree \<Rightarrow> (block_state_type \<times> nat) tree"
        have "\<And>t ta n. t \<notin> bset \<or> ta \<notin> bset \<or> n \<notin> tree.set (tree_map snd t) \<or> n \<notin> tree.set (tree_map snd ta) \<or> ta = t"
          using diff_bset2 id_set_def by auto
        then have "\<exists>t. tt \<notin> bset \<or> tta t \<notin> bset \<or> L b \<notin> tree.set tt \<or> t \<in> bset \<and> tta t = t \<and> L b \<in> tree.set t \<or> t \<in> bset \<and> L b \<in> tree.set t \<and> L b \<notin> tree.set (tta t)"
          by (metis (no_types) image_eqI tree.set_map) }
      then have "\<forall>t. \<exists>ta. \<forall>tb. t \<notin> bset \<or> tb \<notin> bset \<or> L b \<notin> tree.set t \<or> ta \<in> bset \<and> tb = ta \<and> L b \<in> tree.set ta \<or> ta \<in> bset \<and> L b \<in> tree.set ta \<and> L b \<notin> tree.set tb"
        by (metis (no_types))
      then show ?thesis
        by (metis a2)
    qed
  let ?btree = "THE t. t \<in> bset \<and> (L b) \<in> set t \<and> lv = get_level t (L b)"
  have the_btree: "?btree \<in> bset \<and> (L b) \<in> set ?btree \<and> lv = get_level ?btree (L b)"
    using the_P[OF exi_btree] by blast
  have diff_btree: "diff_ids ?btree"
    using the_btree diff_bset1 by auto
  have exi_newb: "\<exists>newb. newb = replace ?btree b (set_state_type b FREE)"
    by simp
  let ?freeblo = "SOME newb. newb = replace ?btree b (set_state_type b FREE)"
  have sub_allocsets: "allocsets ?btree = allocsets ?freeblo \<union> {b}"
    using free_success_sub_allocsets diff_btree a1 a3 the_btree
    proof -
      have "fst (L b) = ALLOC"
        by (metis a3 block_state_type.exhaust)
      then show ?thesis
        using a1 diff_btree free_success_sub_allocsets the_btree by auto
    qed 
  have exi_re: "\<exists>re. re = merge ?freeblo ids"
    by simp
  let ?re = "SOME re. re = merge ?freeblo ids"
  have same_allocsets: "allocsets ?btree = allocsets (fst ?re) \<union> {b}"
    using free_success_same_allocsets sub_allocsets by auto
(*------------------------------------------------------------------------------------------------*)
  have free_re: "(newbset, newids, re) = ((bset - {?btree}) \<union> {fst ?re}, snd ?re, True)"
    using a3 a4 unfolding free_def Let_def using exi_btree by auto
  have step1: "allocsets_pool bset = allocsets_pool (bset - {?btree}) \<union> allocsets ?btree"
    unfolding allocsets_pool_def using the_btree by auto
  have step2: "allocsets_pool newbset = allocsets_pool (bset - {?btree}) \<union> allocsets (fst ?re)"
    unfolding allocsets_pool_def using free_re by auto
  have change_allocsets_pool: "allocsets_pool bset = allocsets_pool newbset \<union> {b}"
    using step1 step2 same_allocsets by auto
  then show ?thesis by auto
qed

end