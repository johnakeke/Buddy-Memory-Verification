theory k_mem_pool
imports Main
begin

subsection \<open>def of datetype\<close>

typedecl Thread
datatype thread_state_type = READY | RUNNING | BLOCKED
datatype timeout_state_type = WAIT | NO_WAIT | FOREVER

datatype block_state_type = FREE | ALLOC
type_synonym ID = "nat"
datatype 'a tree = Leaf 'a | Node (LL:"'a tree") (LR:"'a tree") (RL:"'a tree") (RR:"'a tree")
                            
type_synonym Block = "(nat \<times> block_state_type \<times> ID) tree"
type_synonym Level_Freeset = "(ID set) list"
type_synonym poolname = "string"
record Pool = zerolevelblocklist :: "Block list"
              freelist :: "Level_Freeset"
              n_levels :: "nat"
              nmax :: "nat"
              name :: "poolname"

subsection \<open>def of function_call\<close>

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
  by (smt finite.insertI finite_Collect_not infinite_UNIV_nat insert_compr not_finite_existsD some_eq_ex)

lemma getnewid_diffac:
  "finite ids \<Longrightarrow>
  newid = getnewid ids \<Longrightarrow>
  xa = fst newid \<Longrightarrow>
  xb = fst (snd newid) \<Longrightarrow>
  xc = fst (snd (snd newid)) \<Longrightarrow>
  xd = fst (snd (snd (snd newid))) \<Longrightarrow>
  xa \<noteq> xb \<Longrightarrow>
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
  xa \<noteq> xb \<Longrightarrow>
  xa \<noteq> xc \<Longrightarrow>
  xa \<noteq> xd"
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
  xb \<noteq> xc \<Longrightarrow>
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
  xb \<noteq> xc \<Longrightarrow>
  xb \<noteq> xd \<Longrightarrow>
  xc \<noteq> xd"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ex_new_if_finite finite.insertI infinite_UNIV_nat insertCI some_eq_ex someI_ex)

lemma getnewid_diff2:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid ids) \<Longrightarrow>
  xb = fst (snd (getnewid ids)) \<Longrightarrow>
  xc = fst (snd (snd (getnewid ids))) \<Longrightarrow>
  xd = fst (snd (snd (snd (getnewid ids)))) \<Longrightarrow>
  xb \<noteq> xc \<and> xb \<noteq> xd \<and> xc \<noteq> xd"
  by (meson getnewid_diffbc getnewid_diffbd getnewid_diffcd)

definition getnewid2 :: "ID set \<Rightarrow> (ID \<times> ID set)"
  where "getnewid2 ids \<equiv> let nid = SOME p. p \<notin> ids;
                             nids = ids \<union> {nid} in
                             (nid, nids)"

lemma getnewid2_inc: "ids \<subseteq> snd(getnewid2 ids)"
  unfolding getnewid2_def Let_def by auto

lemma exists_p_getnewid2: "\<exists>p. getnewid2 ids = (p, ids \<union> {p})"
  unfolding getnewid2_def by metis

lemma getnewid2_diff:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid2 ids) \<Longrightarrow>
  xa \<notin> ids"
  unfolding getnewid2_def Let_def
  apply auto
  by (metis Collect_mem_eq finite_Collect_not infinite_UNIV_char_0 not_finite_existsD someI_ex)

definition divide :: "Block \<Rightarrow> Level_Freeset \<Rightarrow> ID set \<Rightarrow> (Block \<times> Level_Freeset \<times> ID set)"
  where "divide b li ids \<equiv> case b of (Leaf v)
                           \<Rightarrow> let level = fst v;
                                  x = snd (snd v);
                                  nids = getnewid ids;
                                  x1 = fst nids;
                                  x2 = fst (snd nids);
                                  x3 = fst (snd (snd nids));
                                  x4 = fst (snd (snd (snd nids)));
                                  newids = snd (snd (snd (snd nids)));
                                  l_freeset = (li ! level) - {x};
                                  nextl_freeset = (li ! (Suc level)) \<union> {x1, x2, x3, x4} in
                                  (Node (Leaf (Suc level, FREE, x1)) (Leaf (Suc level, FREE, x2)) (Leaf (Suc level, FREE, x3)) (Leaf (Suc level, FREE, x4)),
                                  (li[level:=l_freeset])[(Suc level):= nextl_freeset],
                                  newids)"

lemma divide_diff:
  "finite ids \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd (snd ll) \<noteq> snd (snd lr) \<and>
  snd (snd ll) \<noteq> snd (snd rl) \<and>
  snd (snd ll) \<noteq> snd (snd rr)"
  unfolding divide_def Let_def using getnewid_diff1
  by auto

lemma divide_diff2:
  "finite ids \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd (snd lr) \<noteq> snd (snd rl) \<and>
  snd (snd lr) \<noteq> snd (snd rr) \<and>
  snd (snd rl) \<noteq> snd (snd rr)"
  unfolding divide_def Let_def using getnewid_diff2
  by auto

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
  xa \<notin> ids \<Longrightarrow>
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
  xa \<notin> ids \<Longrightarrow>
  xb \<notin> ids \<Longrightarrow>
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
  xa \<notin> ids \<Longrightarrow>
  xb \<notin> ids \<Longrightarrow>
  xc \<notin> ids \<Longrightarrow>
  xd \<notin> ids"
  unfolding getnewid_def Let_def
  apply auto
  by (smt ball_empty empty_Collect_eq ex_new_if_finite finite.insertI infinite_UNIV_nat insert_compr mem_Collect_eq some_eq_ex)

lemma getnewid_diff3:
  "finite ids \<Longrightarrow>
  xa = fst (getnewid ids) \<Longrightarrow>
  xb = fst (snd (getnewid ids)) \<Longrightarrow>
  xc = fst (snd (snd (getnewid ids))) \<Longrightarrow>
  xd = fst (snd (snd (snd (getnewid ids)))) \<Longrightarrow>
  xa \<notin> ids \<and> xb \<notin> ids \<and> xc \<notin> ids \<and> xd \<notin> ids"
  by (simp add: getnewid_anot getnewid_bnot getnewid_cnot getnewid_dnot)

lemma divide_diff3:
  "finite ids \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd (snd ll) \<notin> ids \<and>
  snd (snd lr) \<notin> ids \<and>
  snd (snd rl) \<notin> ids \<and>
  snd (snd rr) \<notin> ids"
  unfolding divide_def Let_def using getnewid_diff3 by auto

definition combine :: "Block \<Rightarrow> Level_Freeset \<Rightarrow> ID set \<Rightarrow> (Block \<times> Level_Freeset \<times> ID set)"
  where "combine b li ids \<equiv> case b of Node (Leaf a1) (Leaf a2) (Leaf a3) (Leaf a4)
                            \<Rightarrow> let x1 = snd (snd a1);
                                   x2 = snd (snd a2);
                                   x3 = snd (snd a3);
                                   x4 = snd (snd a4);
                                   level = fst a1;
                                   nids = getnewid2 ids;
                                   newid = fst nids;
                                   newids = snd nids;
                                   pre_freeset = (li ! (level - 1)) \<union> {newid};
                                   cur_freeset = (li ! level) - {x1, x2, x3, x4} in
                               (Leaf (level - 1, FREE, newid), (li[level:=cur_freeset])[(level - 1):= pre_freeset], newids)"

definition get_blocklevel :: "Block \<Rightarrow> nat"
  where "get_blocklevel b \<equiv> case b of (Leaf a)
                          \<Rightarrow> fst a"

definition get_blocktype :: "Block \<Rightarrow> block_state_type"
  where "get_blocktype b \<equiv> case b of (Leaf a)
                          \<Rightarrow> fst (snd a)"

definition get_blockid :: "Block \<Rightarrow> ID"
  where "get_blockid b \<equiv> case b of (Leaf a)
                          \<Rightarrow> snd (snd a)"

primrec get_leaf :: "Block \<Rightarrow> bool"
  where "get_leaf (Leaf a) = True" |
        "get_leaf (Node ll lr rl rr) = False"
                                                                        
function alloc :: "Block \<Rightarrow> Level_Freeset \<Rightarrow> nat \<Rightarrow> ID set \<Rightarrow> nat \<Rightarrow> (Block \<times> Level_Freeset \<times> ID set \<times> bool)"
  where "alloc (Leaf v) li lv ids curl = (if lv < curl then (Leaf v, li, ids, False)
                                          else 
                                            if lv = curl then
                                              if fst (snd v) = FREE then 
                                                (Leaf (fst v, ALLOC, snd (snd v)),li[lv:=(li ! lv) - {snd (snd v)}], ids, True) 
                                              else (Leaf v, li, ids, False)
                                            else
                                              if fst (snd v) = ALLOC then (Leaf v, li, ids, False)
                                              else
                                                let re = divide (Leaf v) li ids;
                                                    node = fst re;
                                                    freeset = fst (snd re);
                                                    newids = snd (snd re) in
                                                case node of (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) \<Rightarrow>
                                                  let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
                                                    (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True) |
                                                             _ \<Rightarrow> (Leaf v, li, ids, False))" |
        "alloc (Node ll lr rl rr) li lv ids curl = (if lv < Suc curl then (Node ll lr rl rr, li, ids, False)
                                                    else
                                                      let c1 = alloc ll li lv ids (Suc curl) in
                                                      if snd (snd (snd c1)) then (Node (fst c1) lr rl rr, fst (snd c1), fst (snd (snd c1)), True)
                                                      else
                                                        let c2 = alloc lr li lv ids (Suc curl) in
                                                        if snd (snd (snd c2)) then (Node ll (fst c2) rl rr, fst (snd c2), fst (snd (snd c2)), True)
                                                        else
                                                          let c3 = alloc rl li lv ids (Suc curl) in
                                                          if snd (snd (snd c3)) then (Node ll lr (fst c3) rr, fst (snd c3), fst (snd (snd c3)), True)
                                                          else
                                                            let c4 = alloc rr li lv ids (Suc curl) in
                                                            if snd (snd (snd c4)) then (Node ll lr rl (fst c4), fst (snd c4), fst (snd (snd c4)), True)
                                                            else (Node ll lr rl rr, li, ids, False))"
  by pat_completeness auto
termination
  apply(relation "measure (\<lambda>(b, li, lv, ids, curl). lv - curl)")
          apply auto[1]
         apply simp+
  done

function pool_alloc :: "Pool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ID set \<Rightarrow> (Pool \<times> ID set \<times> bool)"
  where "pool_alloc po lv n ids = (if lv < 0 then (po, ids, False)
                                   else
                                     let zeroli = zerolevelblocklist po;
                                         freeli = freelist po;
                                         aa = alloc (zeroli ! n) freeli lv ids 0;
                                         bl = fst aa;
                                         fl = fst (snd aa);
                                         newids = fst (snd (snd aa));
                                         re = snd (snd (snd aa)) in
                                     if re = True \<and> n < length zeroli then
                                       (po\<lparr>zerolevelblocklist := zeroli[n:=bl], freelist := fl\<rparr>, newids, True)
                                     else if re = False \<and> n < (length zeroli - 1) then
                                       pool_alloc po lv (Suc n) ids
                                     else
                                       (po, ids, False))"
  by pat_completeness auto
termination 
  apply(relation "measure (\<lambda>(po, lv, n, ids). (length (zerolevelblocklist po) - n))")
   apply auto
  done

fun free :: "Block \<Rightarrow> Level_Freeset \<Rightarrow> ID \<Rightarrow> ID set \<Rightarrow> (Block \<times> Level_Freeset \<times> ID set \<times> bool)"
  where "free (Leaf v) li num ids = (if fst (snd v) = ALLOC \<and> snd (snd v) = num
                                    then
                                      (Leaf (fst v, FREE, snd (snd v)), li[(fst v):=(li ! (fst v)) \<union> {snd (snd v)}], ids, True)
                                    else
                                      (Leaf v, li, ids, False))" |
        "free (Node ll lr rl rr) li num ids = (let c1 = free ll li num ids in
                                                 if snd (snd (snd c1)) then
                                                   (if (\<exists>la lb lc ld xa xb xc xd. (Node (fst c1) lr rl rr) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                                                   then (let re = combine (Node (fst c1) lr rl rr) (fst (snd c1)) (fst (snd (snd c1)));
                                                             node = fst re;
                                                             freeset = fst (snd re);
                                                             nids = snd (snd re) in (node, freeset, nids, True))
                                                   else (Node (fst c1) lr rl rr, fst (snd c1), (fst (snd (snd c1))), True))
                                                 else
                                                   let c2 = free lr li num ids in
                                                     if snd (snd (snd c2)) then
                                                       (if (\<exists>la lb lc ld xa xb xc xd. (Node ll (fst c2) rl rr) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                                                       then (let re = combine (Node ll (fst c2) rl rr) (fst (snd c2)) (fst (snd (snd c2)));
                                                                 node = fst re;
                                                                 freeset = fst (snd re);
                                                                 nids = snd (snd re) in (node, freeset, nids, True))
                                                       else (Node ll (fst c2) rl rr, fst (snd c2), (fst (snd (snd c2))), True))
                                                     else
                                                       let c3 = free rl li num ids in
                                                         if snd (snd (snd c3)) then
                                                           (if (\<exists>la lb lc ld xa xb xc xd. (Node ll lr (fst c3) rr) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                                                           then let re = combine (Node ll lr (fst c3) rr) (fst (snd c3)) (fst (snd (snd c3)));
                                                                    node = fst re;
                                                                    freeset = fst (snd re);
                                                                    nids = snd (snd re) in (node, freeset, nids, True)
                                                           else (Node ll lr (fst c3) rr, fst (snd c3), (fst (snd (snd c3))), True))
                                                         else
                                                           let c4 = free rr li num ids in
                                                             if snd (snd (snd c4)) then
                                                               (if (\<exists>la lb lc ld xa xb xc xd. (Node ll lr rl (fst c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                                                               then let re = combine (Node ll lr rl (fst c4)) (fst (snd c4)) (fst (snd (snd c4)));
                                                                        node = fst re;
                                                                        freeset = fst (snd re);
                                                                        nids = snd (snd re) in (node, freeset, nids, True)
                                                               else (Node ll lr rl (fst c4), fst (snd c4), (fst (snd (snd c4))), True))
                                                             else (Node ll lr rl rr, li, ids, False))"

function pool_free :: "Pool \<Rightarrow> ID \<Rightarrow> nat \<Rightarrow> ID set \<Rightarrow> (Pool \<times> ID set \<times> bool)"
  where "pool_free po num n ids = (let zeroli = zerolevelblocklist po;
                                       freeli = freelist po;
                                       ff = free (zeroli ! n) freeli num ids;
                                       bl = fst ff;
                                       fl = fst (snd ff);
                                       nids = fst (snd (snd ff));
                                       re = snd (snd (snd ff)) in
                                   if re = True \<and> n < length zeroli then
                                     (po\<lparr>zerolevelblocklist := zeroli[n:= bl], freelist := fl\<rparr>, nids, True)
                                   else if re = False \<and> n < (length zeroli - 1) then
                                     pool_free po num (Suc n) ids
                                   else
                                     (po, ids, False))"
  by pat_completeness auto
termination 
  apply(relation "measure (\<lambda>(po, num, n, ids). (length (zerolevelblocklist po) - n))")
   apply auto
  done

function pool_init :: "Block list \<Rightarrow> ID set \<Rightarrow> ID set \<Rightarrow> nat \<Rightarrow> (Block list \<times> ID set \<times> ID set)"
  where "pool_init bli idl ids num = (let ff = getnewid2 ids;
                                          nid  = fst ff;
                                          nids = snd ff;
                                          b = Leaf(0, FREE, nid);
                                          newbli = bli @ [b];
                                          newidl = idl \<union> {nid} in
                                      if num = 0 then (bli,idl,ids)
                                      else pool_init newbli newidl nids (num - 1))"
  by pat_completeness auto
termination
  apply(relation "measure (\<lambda>(bli, idl, ids, num). num)")
   apply auto
  done

lemma pool_init_n: "\<exists>p. pool_init bli idl ids (Suc n) = pool_init (append bli [Leaf(0, FREE, p)]) (idl \<union> {p}) (ids \<union> {p}) n"
  using pool_init.simps apply auto
  unfolding Let_def getnewid2_def by auto

fun create_freelist :: "nat \<Rightarrow> ID set \<Rightarrow> Level_Freeset"
  where "create_freelist nlv idl = (if nlv = 0 then [idl]
                                     else append (create_freelist (nlv-1) idl) [{}])"

subsection \<open>def of k_mem_pool core function\<close>

record State = t_state :: "Thread \<Rightarrow> thread_state_type"
               pools :: "Pool list"
               waitq :: "Thread \<rightharpoonup> poolname"
               cur :: "Thread option"
               tick :: nat
               idset :: "ID set"

fun idsets_block :: "Block \<Rightarrow> ID set"
  where "idsets_block (Leaf x) = {snd (snd x)}" |
        "idsets_block (Node n1 n2 n3 n4) = idsets_block n1 \<union> idsets_block n2 \<union> idsets_block n3 \<union> idsets_block n4"

definition idsets_pool :: "Pool \<Rightarrow> ID set"
  where "idsets_pool p \<equiv> fold (\<lambda>b ids. ids \<union> idsets_block b) (zerolevelblocklist p) {}"

definition idsets_pools :: "Pool list \<Rightarrow> ID set"
  where "idsets_pools p \<equiv> fold (\<lambda>b ids. ids \<union> idsets_pool b) p {}"

consts s0 :: "State"
specification(s0)
    threadstate: "\<forall>th. t_state s0 th = READY"
    poolsinit: "pools s0 = []"
    waitqinit: "waitq s0 = (\<lambda>x. None)"
    curinit: "cur s0 = None"
    tickinit: "tick s0 = 0"
    idsetinit: "idset s0 = {}"
proof-
  let ?s = "\<lparr>t_state = (\<lambda>th. READY), pools = [], waitq = (\<lambda>th. None), cur = None, tick = 0, idset = {}\<rparr>"
  have "(\<forall>th. t_state ?s th = READY) \<and> pools ?s = [] \<and> waitq ?s = Map.empty \<and> cur ?s = None \<and> tick ?s = 0 \<and> idset ?s = {}" by auto
  then show ?thesis by fastforce
qed

definition time_tick :: "State \<Rightarrow> State"
  where "time_tick s \<equiv> let ti = Suc (tick s) in
                         s\<lparr>tick := ti\<rparr>"

definition schedule :: "State \<Rightarrow> State"
  where "schedule s \<equiv> let t = cur s;
                          news = (case t of None \<Rightarrow> s
                                          | Some th \<Rightarrow> s\<lparr>t_state := (t_state s)(th := READY)\<rparr>);
                          readyset = {t. (t_state news t) = READY} in
                      if readyset = {} then s
                      else let newcur = SOME p. p \<in> readyset in
                           news\<lparr>t_state := (t_state news)(newcur := RUNNING),cur := Some newcur\<rparr>"
                  
definition k_mem_pool_alloc :: "State \<Rightarrow> Pool \<Rightarrow> nat \<Rightarrow> timeout_state_type \<Rightarrow> (State \<times> bool)"
  where "k_mem_pool_alloc s po lv ti \<equiv> if lv < 0 then (s,False)
                                       else
                                         let ts = t_state s;
                                             ps = pools s;
                                             wq = waitq s;
                                             cu = cur s;
                                             ids = idset s;
                                             rpi = pool_alloc po lv 0 ids in
                                         if snd (snd rpi) = True then
                                           (s\<lparr>pools := append (remove1 po ps) [fst rpi],
                                              idset := fst (snd rpi)\<rparr>, True)
                                         else if snd (snd rpi) = False \<and> (ti = WAIT \<or> ti = FOREVER) then
                                            let t = (case cu of None \<Rightarrow> s
                                                              | Some th \<Rightarrow> s\<lparr>t_state := ts(th := BLOCKED),
                                                                            waitq := wq(th := Some (name po)),
                                                                            cur := None\<rparr>) in
                                            (schedule t, False)
                                         else
                                           (s, False)"
    
definition k_mem_pool_free :: "State \<Rightarrow> Pool \<Rightarrow> ID \<Rightarrow> (State \<times> bool)"
  where "k_mem_pool_free s po num \<equiv> let ts = t_state s;
                                         ps = pools s;                       
                                         wq = waitq s;
                                         ids = idset s;
                                         npi = pool_free po num 0 ids in
                                     if snd (snd npi) = True then
                                       let wqth = {t. wq t = Some (name po)} in
                                       if wqth \<noteq> {} then
                                         (s\<lparr>t_state := (\<lambda>t. (if (t \<in> wqth) then READY else (ts t))),
                                            pools := append (remove1 po ps) [fst npi],
                                            waitq := (\<lambda>t. (if (t \<in> wqth) then None else (wq t))),
                                            idset := fst (snd npi)\<rparr>,True)
                                       else
                                         (s\<lparr>pools := (remove1 po ps) @ [fst npi],
                                            idset := fst (snd npi)\<rparr>, True)
                                     else
                                       (s, False)"

definition K_MEM_POOL_DEFINE :: "State \<Rightarrow> poolname \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (State \<times> bool)"
  where "K_MEM_POOL_DEFINE s nam nlv num \<equiv> let ids = idset s;
                                               rpi = pool_init [] {} ids num;
                                               po = \<lparr>zerolevelblocklist = fst rpi,
                                                     freelist = create_freelist (nlv-1) (fst (snd rpi)),
                                                     n_levels = nlv,
                                                     nmax = num,
                                                     name = nam\<rparr>;
                                               ps = pools s in
                                            (s\<lparr>pools := ps @ [po],
                                               idset := snd (snd rpi)\<rparr>, True)"

subsection \<open>def of computation\<close>

type_synonym Trace = "State list"
inductive_set execution :: "Trace set" where
  zero: "[s] \<in> execution" |
  
  init: "\<lbrakk>es \<in> execution; fst (K_MEM_POOL_DEFINE s nam nlv num) = t; t = es ! 0\<rbrakk> \<Longrightarrow>
         s # es \<in> execution" |
  
  alloc1: "\<lbrakk>es \<in> execution; po \<in> set (pools s); fst (k_mem_pool_alloc s po lv ti) = t; t = es ! 0\<rbrakk> \<Longrightarrow>
           s # es \<in> execution" |
  
  free1: "\<lbrakk>es \<in> execution; po \<in> set (pools s); fst (k_mem_pool_free s po num) = t; t = es ! 0\<rbrakk> \<Longrightarrow>
          s # es \<in> execution" |
  
  titi: "\<lbrakk>es \<in> execution; time_tick s = t; t = es ! 0\<rbrakk> \<Longrightarrow>
         s # es \<in> execution" |
  
  sche: "\<lbrakk>es \<in> execution; schedule s = t; t = es ! 0\<rbrakk> \<Longrightarrow>
         s # es \<in> execution"

lemma exec_not_empty: "ts\<in>execution \<Longrightarrow> ts \<noteq> []"
  apply(rule execution.cases)
    apply simp +
  done

definition "reachable s t \<equiv> (\<exists>ts \<in> execution. ts ! 0 = s \<and> last ts = t)"

definition "reachable0 s \<equiv> reachable s0 s"

lemma "reachable0 s0"
  unfolding reachable0_def reachable_def using zero by force

definition "ReachStates \<equiv> {s. reachable0 s}"

subsection \<open>def and proof of inv_cur_state and inv_waitq_state\<close>

definition "inv_cur_waitq \<equiv> {s::State. (\<forall>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING) \<and> (\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED)}"

lemma inv_cur_waitq_s0: "s0 \<in> inv_cur_waitq"
  unfolding s0_def inv_cur_waitq_def using s0_def threadstate waitqinit curinit by auto

lemma inv_cur_waitq_k_mem_pool_define: "s \<in> inv_cur_waitq \<Longrightarrow> fst (K_MEM_POOL_DEFINE s nam nlv num) \<in> inv_cur_waitq"
  unfolding K_MEM_POOL_DEFINE_def Let_def inv_cur_waitq_def by auto

lemma inv_cur_waitq_time_tick: "s \<in> inv_cur_waitq \<Longrightarrow> time_tick s \<in> inv_cur_waitq"
  unfolding time_tick_def Let_def inv_cur_waitq_def by auto

lemma inv_cur_waitq_schedule: "s \<in> inv_cur_waitq \<Longrightarrow> schedule s \<in> inv_cur_waitq"
proof (cases "{t. t_state (case (cur s) of None \<Rightarrow> s | Some th \<Rightarrow> s\<lparr>t_state := (t_state s)(th := READY)\<rparr>) t = READY} = {}")
  case True
  assume a0: "s \<in> inv_cur_waitq"
  have po: "schedule s = s" unfolding schedule_def Let_def
    by (simp add: True)
  have p1: "schedule s \<in> inv_cur_waitq"
    by (simp add: a0 po)
  then show ?thesis by simp 
next
  case False
  assume a1: "s \<in> inv_cur_waitq"
  hence p2: "\<forall>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING"
    and p3: "\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED"
    apply (simp add: inv_cur_waitq_def)
    using \<open>s \<in> inv_cur_waitq\<close> inv_cur_waitq_def by auto
  let ?t ="schedule s"
  {
    have p4: "\<forall>curth. cur ?t = Some curth \<longrightarrow> t_state ?t curth = RUNNING"
      unfolding schedule_def Let_def using False by auto
    fix th
    assume a2: "waitq ?t th \<noteq> None"
    have p5: "waitq s = waitq ?t" unfolding schedule_def Let_def
      by (simp add: option.case_eq_if)
    have p6: "\<forall>t. t_state s t = READY \<longrightarrow> waitq s t = None"
      using p3 by force
    have p7: "\<forall>t. t_state s t = READY \<longrightarrow> waitq ?t t = None"
      using p5 p6 by force
    have p8: "\<forall>t. cur s = Some t \<longrightarrow> waitq ?t t = None"
      using p2 p3 p5 by (metis thread_state_type.distinct(5))
    moreover
    have p9: "t_state s th \<noteq> READY"
      using a2 p7 by auto
    have p10: "t_state s th = BLOCKED"
      by (simp add: a2 p3 p5)
    have p11: "\<forall>t. cur s = Some t \<longrightarrow> t \<noteq> th"
      using a2 p8 by auto
    have p12: "t_state ?t th = BLOCKED"
      using p5 p9 p10 p11 False unfolding schedule_def Let_def
      apply (cases "cur s") apply auto
       apply (metis (mono_tags, lifting) p9 some_eq_ex)
      by (smt p10 p9 some_eq_ex)
    ultimately have p13: "\<forall>t. cur ?t = Some t \<longrightarrow> t_state ?t t = RUNNING \<and> t_state ?t th = BLOCKED"
      using p4 p12 by auto
  }
  then show ?thesis 
    using a1 unfolding schedule_def Let_def inv_cur_waitq_def
    by(smt CollectI State.iffs State.simps(8) State.surjective State.update_convs(4) fun_upd_apply option.case_eq_if option.simps(1))
qed

lemma inv_cur_waitq_k_mem_pool_alloc_helper1:
  "s \<in> inv_cur_waitq \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_cur_waitq"
  unfolding inv_cur_waitq_def
  by (smt State.select_convs(1) State.select_convs(3) State.select_convs(4) State.surjective State.update_convs(2) State.update_convs(6) fst_conv mem_Collect_eq) 

lemma inv_cur_waitq_k_mem_pool_alloc_helper3:
  "s \<in> inv_cur_waitq \<Longrightarrow>
    \<not> snd (snd (let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! 0) (freelist po) lv (idset s) 0; re = snd (snd (snd aa))
                 in if re \<and> zeroli \<noteq> [] then (po\<lparr>zerolevelblocklist := zeroli[0 := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)
                    else if re = False \<and> 0 < length zeroli - 1 then pool_alloc po lv (Suc 0) (idset s) else (po, idset s, False))) \<Longrightarrow>
    schedule (case cur s of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> name po)\<rparr>)) \<in> inv_cur_waitq"
proof-
  assume "s \<in> inv_cur_waitq"
  hence p0: "\<exists>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING"
    and p1: "\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED"
    apply (simp add: inv_cur_waitq_def)
    using \<open>s \<in> inv_cur_waitq\<close> inv_cur_waitq_def by auto
  let ?t = "(case cur s of None \<Rightarrow> s
            | Some th \<Rightarrow> (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> name po),cur := None\<rparr>))"
  {
    have p2: "cur ?t = None"
      by (simp add: option.case_eq_if) 
    from p1 have p3: "\<forall>th. waitq ?t th \<noteq> None \<longrightarrow> t_state ?t th = BLOCKED"
      by (simp add: option.case_eq_if) 
    with p2 have p4: "?t \<in> inv_cur_waitq"
      by (simp add: inv_cur_waitq_def) 
    from p4 have p5: "schedule ?t \<in> inv_cur_waitq"
      by (simp add: inv_cur_waitq_schedule) 
  }
  then show ?thesis by blast
qed

lemma inv_cur_waitq_k_mem_pool_alloc_helper2:
  "s \<in> inv_cur_waitq \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) \<noteq> True \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_cur_waitq" 
  apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
   prefer 2
   apply blast
  apply(simp add:inv_cur_waitq_schedule)
  using inv_cur_waitq_k_mem_pool_alloc_helper3 by blast
  
lemma inv_cur_waitq_k_mem_pool_alloc: "s \<in> inv_cur_waitq \<Longrightarrow> fst (k_mem_pool_alloc s po lv ti) \<in> inv_cur_waitq" 
proof (induct ti)
  case WAIT
    then show ?case unfolding k_mem_pool_alloc_def 
      apply(case_tac "lv < 0")
       apply(simp add:Let_def)
      apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = True")
       apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
        apply(simp add:Let_def)
      using inv_cur_waitq_k_mem_pool_alloc_helper1 inv_cur_waitq_k_mem_pool_alloc_helper2 snd_conv
        unfolding Let_def by simp+
  case FOREVER
    then show ?case unfolding k_mem_pool_alloc_def Let_def
      by (smt State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_cur_waitq\<close> k_mem_pool_alloc_def option.case_eq_if)      
  case NO_WAIT
    then show ?case unfolding k_mem_pool_alloc_def Let_def
      by (simp add: inv_cur_waitq_def)
qed
    
lemma inv_cur_waitq_k_mem_pool_free: "s \<in> inv_cur_waitq \<Longrightarrow> fst (k_mem_pool_free s po num) \<in> inv_cur_waitq"
proof -
  assume a0: "s \<in> inv_cur_waitq"
  hence p0: "\<exists>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING"
    and p1: "\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED"
    apply (simp add: inv_cur_waitq_def)
    using \<open>s \<in> inv_cur_waitq\<close> inv_cur_waitq_def by auto
  let ?t = "fst (k_mem_pool_free s po num)"
  {
    from p1 have p2: "\<forall>t. t_state s t = READY \<longrightarrow> waitq s t = None" by force
    from p0 p1 have p3: "\<exists>t. cur s = Some t \<longrightarrow> waitq s t = None"
      by (metis thread_state_type.distinct(5)) 
    from p2 p3 have p4: "\<exists>t. cur ?t = Some t \<longrightarrow> waitq s t = None" unfolding k_mem_pool_free_def Let_def by simp
    from p0 p4 have p5: "\<exists>t. cur ?t = Some t \<longrightarrow> t_state ?t t = RUNNING" unfolding k_mem_pool_free_def Let_def using fst_conv
      by (smt Collect_empty_eq State.select_convs(1) State.select_convs(4) State.surjective State.update_convs(2) State.update_convs(6) option.distinct(1) option.inject)
    fix th
    assume a1: "waitq ?t th \<noteq> None"
    have p6: "waitq s th \<noteq> None" unfolding k_mem_pool_free_def Let_def using a1 k_mem_pool_free_def
      by (smt State.ext_inject State.surjective State.update_convs(2) State.update_convs(3) State.update_convs(6) old.prod.inject prod.collapse) 
    with p1 have p7: "t_state s th = BLOCKED" by simp
    from p7 have p8: "t_state ?t th = BLOCKED" unfolding k_mem_pool_free_def Let_def using a1 fst_conv empty_def k_mem_pool_free_def
      by (smt Collect_cong State.select_convs(1) State.select_convs(3) State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6))
    from p5 p8 have p9: "\<exists>t. cur ?t = Some t \<longrightarrow> t_state ?t t = RUNNING \<and> t_state ?t th = BLOCKED" by simp
  }     
  then show ?thesis unfolding inv_cur_waitq_def using a0 fst_conv inv_cur_waitq_def k_mem_pool_free_def
    by (smt State.ext_inject State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6) mem_Collect_eq option.simps(3) thread_state_type.distinct(5)) 
qed 
  
lemma inv_cur_waitq_lm_helper: "\<forall>ts. (ts \<in> execution \<and> ts ! 0 \<in> inv_cur_waitq \<longrightarrow> (\<forall>i<length ts. ts ! i \<in> inv_cur_waitq))"
proof -
  {
    fix ts
    assume p0: "ts \<in> execution"
       and p1: "ts ! 0 \<in> inv_cur_waitq"
    then have "\<forall>i<length ts. ts ! i \<in> inv_cur_waitq"
      apply(induct ts)
       apply simp
      using inv_cur_waitq_k_mem_pool_define inv_cur_waitq_k_mem_pool_alloc inv_cur_waitq_k_mem_pool_free inv_cur_waitq_time_tick inv_cur_waitq_schedule
      apply (metis One_nat_def Suc_less_eq Suc_pred length_Cons neq0_conv nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_cur_waitq_k_mem_pool_alloc length_Cons neq0_conv nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_cur_waitq_k_mem_pool_free length_Cons neq0_conv nth_Cons')
      apply (metis (no_types, lifting) One_nat_def diff_less inv_cur_waitq_time_tick length_Cons less_Suc_eq less_le_trans nat_less_le neq0_conv nth.simps nth_Cons' nth_Cons_0)
      by (metis One_nat_def diff_less inv_cur_waitq_schedule length_Cons less_Suc_eq less_le_trans nat_less_le neq0_conv nth_Cons')
  }
  then show ?thesis by auto
qed

lemma inv_cur_waitq_lm: "ReachStates \<subseteq> inv_cur_waitq"
proof -
  {
    fix s
    assume p0: "s \<in> ReachStates"
    hence "reachable0 s" by (simp add:ReachStates_def)
    hence "reachable s0 s" by (simp add:reachable0_def)
    hence "\<exists>ts \<in> execution. ts ! 0 = s0 \<and> last ts = s" by (simp add:reachable_def)
    then obtain ts where a1: "ts \<in> execution" and a2: "ts ! 0 = s0" and a3: "last ts = s" by auto
    hence "s \<in> inv_cur_waitq" using inv_cur_waitq_lm_helper inv_cur_waitq_s0
      by (metis append_butlast_last_id exec_not_empty length_append_singleton lessI nth_append_length)
  }
  then show ?thesis by auto
qed

subsection \<open>def and proof of inv_good_tree\<close>

inductive good_tree :: "Block \<Rightarrow> nat \<Rightarrow> bool"
  where x1: "fst a = n \<Longrightarrow> good_tree (Leaf a) n" |
        x2: "good_tree ll (Suc n) \<and> good_tree lr (Suc n) \<and> good_tree rl (Suc n) \<and> good_tree rr (Suc n) \<Longrightarrow> good_tree (Node ll lr rl rr) n"

inductive_cases good_tree_leaf_node:
  "good_tree (Leaf a) n"
  "good_tree (Node ll lr rl rr) n"

definition "good_tree_valid zerolevel \<equiv> (\<forall>b \<in> set zerolevel. good_tree b 0)"

definition "inv_good_tree \<equiv> {s::State. (\<forall>p \<in> set (pools s). good_tree_valid (zerolevelblocklist p))}"

lemma inv_good_tree_s0: "s0 \<in> inv_good_tree"
  unfolding s0_def inv_good_tree_def good_tree_valid_def
  using s0_def poolsinit by auto

lemma inv_good_tree_time_tick: "s \<in> inv_good_tree \<Longrightarrow> time_tick s \<in> inv_good_tree"
  unfolding time_tick_def Let_def inv_good_tree_def good_tree_valid_def by auto

lemma inv_good_tree_schedule: "s \<in> inv_good_tree \<Longrightarrow> schedule s \<in> inv_good_tree"
  unfolding schedule_def Let_def inv_good_tree_def good_tree_valid_def
  by (simp add: option.case_eq_if)

lemma all_leaf_good_tree: "\<forall>a \<in> set bli. get_leaf a \<and> good_tree a 0 \<Longrightarrow>
                 \<forall>b \<in> set (fst (pool_init bli idl ids num)). get_leaf b \<and> good_tree b 0"
proof(induct "num" arbitrary: bli idl ids)
  case 0
  thus ?case by auto
next
  case (Suc n)
  obtain p where "pool_init bli idl ids (Suc n) = pool_init (bli@[Leaf(0, FREE, p)]) (idl\<union>{p}) (ids\<union>{p}) n"
    using pool_init_n[of "bli" "idl" ids n] by auto
  also have "\<forall>a \<in> set (bli@[Leaf(0, FREE, p)]). get_leaf a \<and> good_tree a 0"
    using Suc(2) x1 by auto
  ultimately show ?case using Suc.hyps by metis
qed

lemma all_leaf_empty_good_tree: "\<forall>b \<in> set (fst (pool_init [] {} ids num)). get_leaf b \<and> good_tree b 0"
proof-
  have "\<forall>a \<in> set []. get_leaf a \<and> good_tree a 0" by auto
  thus ?thesis using all_leaf_good_tree[of "[]" "{}" ids num]
    using all_leaf_good_tree by blast 
qed

lemma inv_good_tree_k_mem_pool_define: "s \<in> inv_good_tree \<Longrightarrow> fst (K_MEM_POOL_DEFINE s nam nlv num) \<in> inv_good_tree"
proof-
  assume "s \<in> inv_good_tree"
  hence p0: "\<forall>p. p \<in> set (pools s) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). good_tree b 0)"
    unfolding inv_good_tree_def good_tree_valid_def by auto
  let ?t = "fst (K_MEM_POOL_DEFINE s nam nlv num)"
  {
    have p1: "butlast (pools ?t) = pools s" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    with p0 have p2: "\<forall>p. p \<in> set (butlast (pools ?t)) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). good_tree b 0)" by auto
    moreover
    have p3: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). get_leaf b \<and> good_tree b 0"
      unfolding K_MEM_POOL_DEFINE_def Let_def using all_leaf_empty_good_tree by auto
    from p3 have p4: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). good_tree b 0" by auto
    moreover
    have p5: "pools ?t = (butlast (pools ?t)) @ [(last (pools ?t))]" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    with p2 p4 have "\<forall>p. p \<in> set (pools ?t) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). good_tree b 0)"
      by (smt butlast.simps(2) butlast_append in_set_butlastD in_set_conv_decomp_last last.simps last_appendR list.distinct(1))  
  }
  then show ?thesis unfolding inv_good_tree_def 
    by (simp add: good_tree_valid_def)
qed

lemma good_tree_alloc_leaf_case1:
  "lv < curl \<Longrightarrow>
  good_tree (Leaf x) curl \<Longrightarrow>
  good_tree (fst (alloc (Leaf x) li lv ids curl)) curl"
  by auto

lemma good_tree_alloc_leaf_case2:
  "\<not> lv < curl \<Longrightarrow>
  lv = curl \<Longrightarrow>
  good_tree (Leaf x) curl \<Longrightarrow>
  good_tree (fst (alloc (Leaf x) li lv ids curl)) curl"
  apply auto
  by (metis fst_conv good_tree_leaf_node(1) x1)
  
lemma good_tree_alloc_leaf_case3:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) = ALLOC \<Longrightarrow>
  good_tree (Leaf x) curl \<Longrightarrow>
  good_tree (fst (alloc (Leaf x) li lv ids curl)) curl"
  by auto

lemma inv_alloc_leaf_h:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newli = fst (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  newids = snd (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) newli lv newids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
proof-
  assume a0: "\<not> lv < curl"
     and a1: "lv \<noteq> curl"
     and a2: "fst (snd x) \<noteq> ALLOC"
     and a3: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
     and a4: "newli = fst (snd (divide (Leaf x) li ids))"
     and a5: "newids = snd (snd (divide (Leaf x) li ids))"
  let ?p = "let re = divide (Leaf x) li ids;
                node = fst re;
                freeset = fst (snd re);
                newids = snd (snd re) in
            case node of (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) \<Rightarrow>
              let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
              (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True) |
                         _ \<Rightarrow> (Leaf x, li, ids, False)"
  have p0: "fst (alloc (Leaf x) li lv ids curl) = fst ?p" using a0 a1 a2 by auto
  let ?b = "let re = divide (Leaf x) li ids;
                node = fst re;
                freeset = fst (snd re);
                newids = snd (snd re) in
            (let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
              (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True))"
  have p1: "?p = ?b" unfolding Let_def using a3 by auto
  let ?newli = "fst (snd (divide (Leaf x) li ids))"
  let ?newids = "snd (snd (divide (Leaf x) li ids))"
  have p2: "fst ?b = Node (fst (alloc (Leaf ll) ?newli lv ?newids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
    unfolding Let_def by auto
  have p3: "fst ?p = Node (fst (alloc (Leaf ll) ?newli lv ?newids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
    using p1 p2 by auto
  have p4: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?newli lv ?newids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
    using p0 p3 by auto
  then show ?thesis using a4 a5 by auto
qed

lemma good_tree_alloc_leaf_case4:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  good_tree (Leaf x) curl \<Longrightarrow>
  good_tree (fst (alloc (Leaf x) li lv ids curl)) curl"
proof(induct "lv - curl" arbitrary: curl x li ids)
  case 0
  then show ?case by linarith
next
  case (Suc xa)
  have leaf_level: "fst x = curl" using Suc(6) good_tree_leaf_node(1) by blast
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and ll_level: "fst ll = Suc (fst x)"
      and lr_level: "fst lr = Suc (fst x)"
      and rl_level: "fst rl = Suc (fst x)"
      and rr_level: "fst rr = Suc (fst x)"
      and pll_alloc: "fst (snd ll) \<noteq> ALLOC"
      and pll_free: "fst (snd ll) = FREE"
    unfolding divide_def Let_def by auto
  from ll_level have good_ll: "good_tree (Leaf ll) (Suc curl)"
    using leaf_level by (simp add: x1)
  from lr_level have good_lr: "good_tree (Leaf lr) (Suc curl)"
    using leaf_level by (simp add: x1)
  from rl_level have good_rl: "good_tree (Leaf rl) (Suc curl)"
    using leaf_level by (simp add: x1)
  from rr_level have good_rr: "good_tree (Leaf rr) (Suc curl)"
    using leaf_level by (simp add: x1)
  let ?li = "fst (snd (divide (Leaf x) li ids))"
  let ?ids = "snd (snd (divide (Leaf x) li ids))"
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_curl: "\<not> lv < curl" using lv_suc_curl by auto
    have de_lv_eq_curl: "\<not> lv = curl" using lv_suc_curl by auto
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto
    have step1: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h de_lv_less_curl de_lv_eq_curl Suc(5) pdivide by auto
    have ll_alloc: "fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)) = Leaf (fst ll, ALLOC, snd (snd ll))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free by auto
    have good_ll_alloc: "good_tree (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Suc curl)"
      using ll_alloc leaf_level ll_level by (simp add: x1)
    have good_x_alloc: "good_tree (fst (alloc (Leaf x) li lv ids curl)) curl"
      using step1 good_ll_alloc good_lr good_rl good_rr by (simp add:x2)
    then have ?case by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(3,4) by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have step2: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h Suc(3,4,5) pdivide by auto
    have good_tree_ll_alloc: "good_tree (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Suc curl)"
      using Suc(1) xa_lv_suc_curl de_lv_less_suc_curl de_lv_suc_curl pll_alloc good_ll by auto
    have good_tree_x_alloc: "good_tree (fst (alloc (Leaf x) li lv ids curl)) curl"
      using step2 good_tree_ll_alloc good_lr good_rl good_rr by (simp add:x2)
    then have ?case by auto
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma good_tree_alloc_node_h:
  "good_tree b curl \<Longrightarrow>
  lv = curl \<Longrightarrow>
  good_tree (fst (alloc b li lv ids curl)) curl"
proof(induct b)
  case (Leaf x)
  then show ?case using good_tree_alloc_leaf_case2 by auto
next
  case (Node b1 b2 b3 b4)
  have good_node: "good_tree (Node b1 b2 b3 b4) curl" by (simp add: Node.prems(1)) 
  assume a0: "lv = curl"
  have lv_le_suc_curl: "lv < Suc curl" using a0 by auto
  have "good_tree (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) curl"
    using alloc.simps(2) lv_le_suc_curl good_node by auto
  then show ?case by auto
qed

lemma good_tree_alloc_node:
  "good_tree (Node b1 b2 b3 b4) curl \<Longrightarrow>
  \<not> lv < Suc curl \<Longrightarrow>
  good_tree (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) curl"
proof(induct "lv - curl" arbitrary: curl b1 b2 b3 b4 li ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have good_b1: "good_tree b1 (Suc curl)"
    using Suc(3) good_tree_leaf_node(2) by blast
  have good_b2: "good_tree b2 (Suc curl)"
    using Suc(3) good_tree_leaf_node(2) by blast
  have good_b3: "good_tree b3 (Suc curl)"
    using Suc(3) good_tree_leaf_node(2) by blast
  have good_b4: "good_tree b4 (Suc curl)"
    using Suc(3) good_tree_leaf_node(2) by blast
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b1: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    have good_alloc_b1: "good_tree (fst (alloc b1 li lv ids (Suc curl))) (Suc curl)"
      using good_tree_alloc_node_h good_b1 lv_suc_curl by auto
    have good_node_b1: "good_tree (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) curl"
      using good_alloc_b1 good_b2 good_b3 good_b4 by (simp add: x2)
    have ?case using alloc_b1 good_node_b1 by auto
    }moreover
    {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b2: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    have good_alloc_b2: "good_tree (fst (alloc b2 li lv ids (Suc curl))) (Suc curl)"
      using good_tree_alloc_node_h good_b2 lv_suc_curl by auto
    have good_node_b2: "good_tree (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) curl"
      using good_alloc_b2 good_b1 good_b3 good_b4 by (simp add: x2)
    have ?case using alloc_b2 good_node_b2 by auto
    }moreover
    {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b3: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    have good_alloc_b3: "good_tree (fst (alloc b3 li lv ids (Suc curl))) (Suc curl)"
      using good_tree_alloc_node_h good_b3 lv_suc_curl by auto
    have good_node_b3: "good_tree (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) curl"
      using good_alloc_b3 good_b1 good_b2 good_b4 by (simp add: x2)
    have ?case using alloc_b3 good_node_b3 by auto
    }moreover
    {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b4: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    have good_alloc_b4: "good_tree (fst (alloc b4 li lv ids (Suc curl))) (Suc curl)"
      using good_tree_alloc_node_h good_b4 lv_suc_curl by auto
    have good_node_b4: "good_tree (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) curl"
      using good_alloc_b4 good_b1 good_b2 good_b3 by (simp add: x2)
    have ?case using alloc_b4 good_node_b4 by auto
    }moreover
    {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have step5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    then have ?case using Suc(3) by auto
    }
    ultimately have ?case by blast
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_le_suc_suc_curl: "\<not> lv < Suc (Suc curl)" using xa_gr_1 xa_lv_suc_curl by auto
    have lv_gr_suc_curl: "lv > Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_gr_suc_curl by auto
    have de_lv_eq_suc_curl: "lv \<noteq> Suc curl" using lv_gr_suc_curl by auto

    {assume c11: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b11: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using Suc(4) c11 by auto
    have good_alloc_b11: "good_tree (fst (alloc b1 li lv ids (Suc curl))) (Suc curl)"
      using Suc(1) xa_lv_suc_curl good_b1 de_lv_le_suc_suc_curl
      by (metis Suc.prems(2) good_tree.simps good_tree_alloc_leaf_case3 good_tree_alloc_leaf_case4 not_less_less_Suc_eq)
    have good_node_b11: "good_tree (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) curl"
      using good_alloc_b11 good_b2 good_b3 good_b4 by (simp add: x2)
    have ?case using alloc_b11 good_node_b11 by auto
    }moreover
    {assume c22: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b22: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using Suc(4) c22 by auto
    have good_alloc_b22: "good_tree (fst (alloc b2 li lv ids (Suc curl))) (Suc curl)"
      using Suc(1) xa_lv_suc_curl good_b2 de_lv_le_suc_suc_curl
      by (metis Suc.prems(2) good_tree.simps good_tree_alloc_leaf_case3 good_tree_alloc_leaf_case4 not_less_less_Suc_eq)
    have good_node_b22: "good_tree (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) curl"
      using good_alloc_b22 good_b1 good_b3 good_b4 by (simp add: x2)
    have ?case using alloc_b22 good_node_b22 by auto
    }moreover
    {assume c33: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b33: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using Suc(4) c33 by auto
    have good_alloc_b33: "good_tree (fst (alloc b3 li lv ids (Suc curl))) (Suc curl)"
      using Suc(1) xa_lv_suc_curl good_b3 de_lv_le_suc_suc_curl
      by (metis Suc.prems(2) good_tree.simps good_tree_alloc_leaf_case3 good_tree_alloc_leaf_case4 not_less_less_Suc_eq)
    have good_node_b33: "good_tree (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) curl"
      using good_alloc_b33 good_b1 good_b2 good_b4 by (simp add: x2)
    have ?case using alloc_b33 good_node_b33 by auto
    }moreover
    {assume c44: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b44: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using Suc(4) c44 by auto
    have good_alloc_b44: "good_tree (fst (alloc b4 li lv ids (Suc curl))) (Suc curl)"
      using Suc(1) xa_lv_suc_curl good_b4 de_lv_le_suc_suc_curl
      by (metis Suc.prems(2) good_tree.simps good_tree_alloc_leaf_case3 good_tree_alloc_leaf_case4 not_less_less_Suc_eq)
    have good_node_b44: "good_tree (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) curl"
      using good_alloc_b44 good_b1 good_b2 good_b3 by (simp add: x2)
    have ?case using alloc_b44 good_node_b44 by auto
    }moreover
    {assume c55: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have step5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    then have ?case using Suc(3) by auto
    }
    ultimately have ?case by blast
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma inv_good_tree_alloc:
  "good_tree b curl \<Longrightarrow>
  snd (snd (snd (alloc b li lv ids curl))) = True \<Longrightarrow>
  good_tree (fst (alloc b li lv ids curl)) curl"
proof(induct b)
  case (Leaf x)
  then show ?case using good_tree_alloc_leaf_case1 good_tree_alloc_leaf_case2 good_tree_alloc_leaf_case3 good_tree_alloc_leaf_case4
    by metis
next
  case (Node b1 b2 b3 b4)
  then show ?case using good_tree_alloc_node by auto
qed

lemma pool_alloc_good_tree_case1:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
proof-
  assume a0: "good_tree_valid (zerolevelblocklist po)"
     and a1: "\<not> lv < 0"
     and a2: "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). good_tree b 0" using a0 good_tree_valid_def by auto
  have p1: "good_tree (zerolevelblocklist po ! n) 0" using p0 a2 by auto
  have p2: "good_tree (fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)) 0" using p1 a2 inv_good_tree_alloc by auto
  let ?po = "let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! n) (freelist po) lv ids 0
            in po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>"
  {
    have p3: "fst (pool_alloc po lv n ids) = ?po" apply simp using a2 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist ?po ! n) = fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)" unfolding Let_def using a2 by auto
    then have p5: "good_tree (zerolevelblocklist ?po ! n) 0" using p2 unfolding Let_def by auto
    with p0 have p6: "\<forall>b \<in> set (zerolevelblocklist ?po). good_tree b 0" unfolding Let_def apply auto
      by (metis in_set_conv_nth length_list_update nth_list_update_neq p0)
    have p7: "good_tree_valid (zerolevelblocklist ?po)" unfolding good_tree_valid_def using p6 by auto
    with p3 have p8: "good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_alloc_good_tree_case3:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
  by auto

lemma pool_alloc_good_tree_case2:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith
next
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto
  have step: "pool_alloc po lv n ids = pool_alloc po lv (Suc n) ids" using Suc by auto
  { 
    assume a00: "snd (snd (snd (alloc ((zerolevelblocklist po) ! (Suc n)) (freelist po) lv ids 0))) = False \<and> (Suc n) < length (zerolevelblocklist po) - 1"
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith  
    ultimately have "good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv (Suc n) ids)))"
      using Suc.hyps(1) Suc.prems(1) by blast
  }
  moreover
  have "good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv (Suc n) ids)))"
    using Suc.prems(1) pool_alloc_good_tree_case1 pool_alloc_good_tree_case3 calculation by blast    
  ultimately show ?case using step by auto
qed

lemma inv_good_tree_pool_alloc:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
  apply(cases "lv < 0") apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)")
  using pool_alloc_good_tree_case1[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_alloc_good_tree_case3[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  using pool_alloc_good_tree_case2[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] by simp

lemma inv_good_tree_k_mem_pool_alloc_helper1:
  "s \<in> inv_good_tree \<and> po \<in> set (pools s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_good_tree"
proof-
  assume a0: "s \<in> inv_good_tree \<and> po \<in> set (pools s)"
  hence p0: "\<forall>p \<in> set (pools s). good_tree_valid (zerolevelblocklist p)"
    by (simp add: inv_good_tree_def)
  hence p1: "good_tree_valid (zerolevelblocklist po)"
    by (simp add: a0)
  let ?rpi = "pool_alloc po lv 0 (idset s)"
  have p2: "good_tree_valid (zerolevelblocklist (fst ?rpi))" using inv_good_tree_pool_alloc p1 by blast
  moreover
  have p3: "\<forall>p \<in> set ((remove1 po (pools s)) @ [fst ?rpi]). good_tree_valid (zerolevelblocklist p)" using p0 p2 by auto
  let ?s = "s\<lparr>pools := remove1 po (pools s) @ [fst ?rpi], idset := fst (snd ?rpi)\<rparr>"
  have p4: "?s \<in> inv_good_tree"
    unfolding inv_good_tree_def using p3 by auto
  then show "s \<in> inv_good_tree \<and> po \<in> set (pools s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_good_tree"
    by (smt fst_conv)
qed

lemma inv_good_tree_k_mem_pool_alloc_helper3:
  "s \<in> inv_good_tree \<Longrightarrow>
    \<not> snd (snd (let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! 0) (freelist po) lv (idset s) 0; re = snd (snd (snd aa))
                 in if re \<and> zeroli \<noteq> [] then (po\<lparr>zerolevelblocklist := zeroli[0 := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)
                    else if re = False \<and> 0 < length zeroli - 1 then pool_alloc po lv (Suc 0) (idset s) else (po, idset s, False))) \<Longrightarrow>
    schedule (case cur s of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> name po)\<rparr>)) \<in> inv_good_tree"
proof-
  assume "s \<in> inv_good_tree"
  hence p0: "\<forall>p \<in> set (pools s). good_tree_valid (zerolevelblocklist p)"
    using inv_good_tree_def by blast
  let ?t = "case (cur s) of None \<Rightarrow> s
                    | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := (waitq s)(th \<mapsto> name po)\<rparr>)"
  {
    have p1: "pools s = pools ?t" by (simp add: option.case_eq_if)
    with p0 have p2: "\<forall>p \<in> set (pools ?t). good_tree_valid (zerolevelblocklist p)" by simp
    from p2 have p3: "?t \<in> inv_good_tree"
      by (simp add: inv_good_tree_def)
    from p3 have p4: "schedule ?t \<in> inv_good_tree" by (simp add:inv_good_tree_schedule)
  }
  then show ?thesis by blast
qed

lemma inv_good_tree_k_mem_pool_alloc_helper2:
  "s \<in> inv_good_tree \<and> po \<in> set (pools s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) \<noteq> True \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_good_tree"
  apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
   prefer 2
   apply blast
  apply(simp add:inv_good_tree_schedule)
  using inv_good_tree_k_mem_pool_alloc_helper3 by blast

lemma inv_good_tree_k_mem_pool_alloc: "s \<in> inv_good_tree \<and> po \<in> set (pools s) \<Longrightarrow> fst (k_mem_pool_alloc s po lv ti) \<in> inv_good_tree"
proof (induct ti)
  case WAIT
  then show ?case unfolding k_mem_pool_alloc_def
    apply(case_tac "lv < 0")
     apply(simp add:Let_def)
    apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = True")
       apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
      apply(simp add:Let_def)
    using inv_good_tree_k_mem_pool_alloc_helper1 inv_good_tree_k_mem_pool_alloc_helper2 snd_conv
      unfolding Let_def by simp+
  case FOREVER
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_good_tree\<close> k_mem_pool_alloc_def option.case_eq_if)
  case NO_WAIT
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(2) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_good_tree\<close> fst_conv k_mem_pool_alloc_def timeout_state_type.distinct(1) timeout_state_type.distinct(5))
qed

lemma good_tree_combine:
  "b = Node (Leaf (Suc lv, FREE, xa)) (Leaf (Suc lv, FREE, xb)) (Leaf (Suc lv, FREE, xc)) (Leaf (Suc lv, FREE, xd)) \<Longrightarrow>
  good_tree (fst (combine b li ids)) lv"
  unfolding combine_def Let_def
  by (simp add: x1)

lemma inv_good_tree_free:
  "good_tree b curl \<Longrightarrow>
  snd (snd (snd (free b li num ids))) = True \<Longrightarrow>
  good_tree (fst (free b li num ids)) curl"
proof(induct b arbitrary: curl)
  case (Leaf x)
  then show ?case
    apply auto
    by (metis fst_conv good_tree_leaf_node(1) x1)
next
  case (Node b1 b2 b3 b4)
  assume good_node: "good_tree (Node b1 b2 b3 b4) curl"
  have good_b1: "good_tree b1 (Suc curl)"
    using good_node good_tree_leaf_node(2) by blast
  have good_b2: "good_tree b2 (Suc curl)"
    using good_node good_tree_leaf_node(2) by blast
  have good_b3: "good_tree b3 (Suc curl)"
    using good_node good_tree_leaf_node(2) by blast
  have good_b4: "good_tree b4 (Suc curl)"
    using good_node good_tree_leaf_node(2) by blast

  {assume c1: "snd (snd (snd (free b1 li num ids)))"
    let ?c1 = "free b1 li num ids"
    let ?step1 = "if (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node (fst ?c1) b2 b3 b4, fst (snd ?c1), (fst (snd (snd ?c1))), True)"
    have step1: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step1"
      unfolding free.simps(2) Let_def using c1 by auto
    have good_tree_b1: "good_tree (fst ?c1) (Suc curl)"
      using good_b1 c1 Node.hyps(1) by auto
    have good_node_b1: "good_tree (Node (fst ?c1) b2 b3 b4) curl"
      using good_tree_b1 good_b2 good_b3 good_b4 by (simp add: x2)    
    have "good_tree (fst ?step1) curl"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step1 = fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have leaf_la: "la = Suc curl" using good_tree_b1
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lb: "lb = Suc curl" using good_b2
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lc: "lc = Suc curl" using good_b3
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_ld: "ld = Suc curl" using good_b4
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have good_case0: "good_tree (fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))) curl"
          using good_tree_combine ob_case0 leaf_la leaf_lb leaf_lc leaf_ld by auto
        have "good_tree (fst ?step1) curl"
          using step_case0 good_case0 by auto
        then have ?thesis by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step1 = Node (fst ?c1) b2 b3 b4"
          unfolding free.simps(2) Let_def using case1 by auto
        have "good_tree (fst ?step1) curl"
          using step_case1 good_node_b1 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step1 by auto
  }moreover
  {assume c2: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids)))"
    let ?c2 = "free b2 li num ids"
    let ?step2 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 (fst ?c2) b3 b4, fst (snd ?c2), (fst (snd (snd ?c2))), True)"
    have step2: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step2"
      unfolding free.simps(2) Let_def using c2 by auto
    have good_tree_b2: "good_tree (fst (free b2 li num ids)) (Suc curl)"
      using good_b2 c2 Node.hyps(2) by auto
    have good_node_b2: "good_tree (Node b1 (fst ?c2) b3 b4) curl"
      using good_tree_b2 good_b1 good_b3 good_b4 by (simp add: x2)
    have "good_tree (fst ?step2) curl"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step2 = fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have leaf_la: "la = Suc curl" using good_b1
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lb: "lb = Suc curl" using good_tree_b2
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lc: "lc = Suc curl" using good_b3
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_ld: "ld = Suc curl" using good_b4
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have good_case0: "good_tree (fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))) curl"
          using good_tree_combine ob_case0 leaf_la leaf_lb leaf_lc leaf_ld by auto
        have "good_tree (fst ?step2) curl"
          using step_case0 good_case0 by auto
        then have ?thesis by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step2 = Node b1 (fst ?c2) b3 b4"
          unfolding free.simps(2) Let_def using case1 by auto
        have "good_tree (fst ?step2) curl"
          using step_case1 good_node_b2 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis  by auto
    qed
    then have ?case using step2 by auto
  }moreover
  {assume c3: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids)))"
    let ?c3 = "free b3 li num ids"
    let ?step3 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 (fst ?c3) b4, fst (snd ?c3), (fst (snd (snd ?c3))), True)"
    have step3: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step3"
      unfolding free.simps(2) Let_def using c3 by auto
    have good_tree_b3: "good_tree (fst (free b3 li num ids)) (Suc curl)"
      using good_b3 c3 Node.hyps(3) by auto
    have good_node_b3: "good_tree (Node b1 b2 (fst ?c3) b4) curl"
      using good_tree_b3 good_b1 good_b2 good_b4 by (simp add: x2)
    have "good_tree (fst ?step3) curl"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step3 = fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have leaf_la: "la = Suc curl" using good_b1
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lb: "lb = Suc curl" using good_b2
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lc: "lc = Suc curl" using good_tree_b3
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_ld: "ld = Suc curl" using good_b4
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have good_case0: "good_tree (fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))) curl"
          using good_tree_combine ob_case0 leaf_la leaf_lb leaf_lc leaf_ld by auto
        have "good_tree (fst ?step3) curl"
          using step_case0 good_case0 by auto
        then have ?thesis by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step3 = Node b1 b2 (fst ?c3) b4"
          unfolding free.simps(2) Let_def using case1 by auto
        have "good_tree (fst ?step3) curl"
          using step_case1 good_node_b3 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step3 by auto
  }moreover
  {assume c4: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids)))"
    let ?c4 = "free b4 li num ids"
    let ?step4 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 b3 (fst ?c4), fst (snd ?c4), (fst (snd (snd ?c4))), True)"
    have step4: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step4"
      unfolding free.simps(2) Let_def using c4 by auto
    have good_tree_b4: "good_tree (fst (free b4 li num ids)) (Suc curl)"
      using good_b4 c4 Node.hyps(4) by auto
    have good_node_b4: "good_tree (Node b1 b2 b3 (fst ?c4)) curl"
      using good_tree_b4 good_b1 good_b2 good_b3 by (simp add: x2)
    have "good_tree (fst ?step4) curl"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step4 = fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have leaf_la: "la = Suc curl" using good_b1
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lb: "lb = Suc curl" using good_b2
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_lc: "lc = Suc curl" using good_b3
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have leaf_ld: "ld = Suc curl" using good_tree_b4
          using ob_case0 good_tree_leaf_node(1) by fastforce
        have good_case0: "good_tree (fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))) curl"
          using good_tree_combine ob_case0 leaf_la leaf_lb leaf_lc leaf_ld by auto
        have "good_tree (fst ?step4) curl"
          using step_case0 good_case0 by auto
        then have ?thesis by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step4 = Node b1 b2 b3 (fst ?c4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have "good_tree (fst ?step4) curl"
          using step_case1 good_node_b4 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step4 by auto
  }moreover
  {assume c5: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids))) = False"
    have step5: "fst (free (Node b1 b2 b3 b4) li num ids) = (Node b1 b2 b3 b4)"
      unfolding free.simps(2) Let_def using c5 by auto
    then have ?case using good_node by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma pool_free_good_tree_case1:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
proof-
  assume a0: "good_tree_valid (zerolevelblocklist po)"
     and a1: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). good_tree b 0" using a0 good_tree_valid_def by auto
  have p1: "good_tree (zerolevelblocklist po ! n) 0" using p0 a1 by auto
  have p2: "good_tree (fst (free (zerolevelblocklist po ! n) (freelist po) num ids)) 0" using p1 a1 inv_good_tree_free by auto
  let ?po = "let zeroli = zerolevelblocklist po; aa = free (zeroli ! n) (freelist po) num ids
            in po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>"
  {
    have p3: "fst (pool_free po num n ids) = ?po" apply simp using a1 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist ?po ! n) = fst (free (zerolevelblocklist po ! n) (freelist po) num ids)" unfolding Let_def using a1 by auto
    then have p5: "good_tree (zerolevelblocklist ?po ! n) 0" using p2 unfolding Let_def by auto
    with p0 have p6: "\<forall>b \<in> set (zerolevelblocklist ?po). good_tree b 0" unfolding Let_def apply auto
      by (metis in_set_conv_nth length_list_update nth_list_update_neq p0)
    have p7: "good_tree_valid (zerolevelblocklist ?po)" unfolding good_tree_valid_def using p6 by auto
    with p3 have p8: "good_tree_valid (zerolevelblocklist (fst (pool_free po num n ids)))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_free_good_tree_case3:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
  by auto

lemma pool_free_good_tree_case2:
  "good_tree_valid (zerolevelblocklist po) \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  good_tree_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith 
next 
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto     
  have step: "pool_free po num n ids = pool_free po num (Suc n) ids" using Suc by auto
  { 
    assume a00: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1) "
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith   
    ultimately have "good_tree_valid (zerolevelblocklist (fst (pool_free po num (Suc n) ids)))"
      using Suc.hyps(1) Suc.prems(1) pool_free_good_tree_case1 pool_free_good_tree_case3 by blast
  }    
  moreover 
  have "good_tree_valid (zerolevelblocklist (fst (pool_free po num (Suc n) ids)))"
    using Suc.prems(2) calculation by blast 
  ultimately show ?case using step by auto
qed

lemma inv_good_tree_pool_free: "good_tree_valid (zerolevelblocklist po) \<Longrightarrow> good_tree_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)")
  using pool_free_good_tree_case1[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_free_good_tree_case3[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  using pool_free_good_tree_case2[where po = "po" and num = "num" and n = "n" and ids = "ids"] by simp

lemma pool_free_lm_helper: "snd (snd (pool_free po num n ids)) = False \<longrightarrow> fst (pool_free po num n ids) = po"
  apply(induct_tac rule:pool_free.induct)
  apply(rule impI)
  apply simp
  apply(case_tac "snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) \<and> n < length (zerolevelblocklist po)")
   apply (smt snd_conv)
  apply(case_tac "snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   apply simp
  by(smt fst_conv)

lemma pool_free_lm: "pool_free po num n ids = re \<Longrightarrow> snd (snd re) = False \<Longrightarrow> fst re = po"
  using pool_free_lm_helper by auto

lemma inv_block_k_mem_pool_free_helper: 
  "snd (snd (pool_free po num 0 (idset s))) \<noteq> True \<Longrightarrow>
      (let ts = t_state s; ps = pools s; wq = waitq s; ids = idset s;
                         npi = pool_free po num 0 ids
                     in if snd (snd npi) = True
                        then let wqth = {t. wq t = Some (name po)}
                             in if wqth \<noteq> {}
                                then (s\<lparr>t_state := \<lambda>t. if t \<in> wqth then READY else ts t, pools := remove1 po ps @ [fst npi],
                                          waitq := \<lambda>t. if t \<in> wqth then None else wq t, idset := fst (snd npi)\<rparr>,
                                      True)
                                else (s\<lparr>pools := remove1 po ps @ [fst npi], idset := fst (snd npi)\<rparr>, True)
                        else (s, False)) = (s, False)"
  by (simp add:Let_def)
  
lemma set_helper: "po \<in> set l \<Longrightarrow> set ((remove1 po l) @ [po]) = set l"
  by (smt append_assoc remove1.simps(2) remove1_append rotate1.simps(2) set_append set_rotate1 split_list_first)

lemma inv_good_tree_k_mem_pool_free: "po \<in> set (pools s) \<and> s \<in> inv_good_tree \<Longrightarrow> fst (k_mem_pool_free s po num) \<in> inv_good_tree"
proof-
  assume a0: "po \<in> set (pools s) \<and> s \<in> inv_good_tree"
  hence p0: "\<forall>p \<in> set (pools s). good_tree_valid (zerolevelblocklist p)" unfolding inv_good_tree_def by auto
  from a0 p0 have p1: "good_tree_valid (zerolevelblocklist po)" by simp 
  let ?po1 = "fst (pool_free po num 0 (idset s))"
  from p1 have p2: "good_tree_valid (zerolevelblocklist ?po1)"
    using inv_good_tree_pool_free[where po = "po" and num = "num" and n = 0 and ids = "idset s"] by auto
  let ?t = "fst (k_mem_pool_free s po num)"
  {
    have p3: "set (pools ?t) = set (append (remove1 po (pools s)) [?po1])"
      unfolding k_mem_pool_free_def
      apply(case_tac "snd (snd (pool_free po num 0 (idset s))) = True")
       apply(case_tac "{t. (waitq s) t = Some (name po)} \<noteq> {}")
        apply(simp add:Let_def)
       apply(simp add:Let_def)
      using inv_block_k_mem_pool_free_helper[of po num s]
      pool_free_lm[where po = "po" and num = "num" and n = 0 and ids = "idset s" and re="pool_free po num 0 (idset s)"]
      set_helper[of po "pools s"]
      snd_conv fst_conv a0 by simp
    fix pl
    assume a1: "pl \<in> set (pools ?t)" 
    have p4: "good_tree_valid (zerolevelblocklist pl)"
      proof(cases "pl = ?po1")
        assume "pl = ?po1"
        with p2 show ?thesis by simp
      next
        assume "pl \<noteq> ?po1"
        with p0 p3 a1 show ?thesis by force
      qed
  }
  then show ?thesis unfolding inv_good_tree_def by force
qed

lemma inv_good_tree_lm_helper: "\<forall>ts. (ts \<in> execution \<and> ts ! 0 \<in> inv_good_tree \<longrightarrow> (\<forall>i<length ts. ts ! i \<in> inv_good_tree))"
proof -
  {
    fix ts
    assume p0: "ts \<in> execution"
       and p1: "ts ! 0 \<in> inv_good_tree"
    then have "\<forall>i<length ts. ts ! i \<in> inv_good_tree"
      apply(induct ts)
       apply simp
      using inv_good_tree_k_mem_pool_define inv_good_tree_k_mem_pool_alloc inv_good_tree_k_mem_pool_free inv_good_tree_time_tick inv_good_tree_schedule
      apply (metis One_nat_def Suc_less_eq Suc_pred length_Cons neq0_conv nth.simps nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_good_tree_k_mem_pool_alloc length_Cons neq0_conv nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_good_tree_k_mem_pool_free length_Cons neq0_conv nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_good_tree_time_tick length_Cons neq0_conv nth_Cons')
      by (metis One_nat_def Suc_less_eq Suc_pred inv_good_tree_schedule length_Cons neq0_conv nth_Cons')   
  }
  then show ?thesis by auto
qed
  
lemma inv_good_tree_lm: "ReachStates \<subseteq> inv_good_tree"
proof -
  {
    fix s
    assume p0: "s \<in> ReachStates"
    hence "reachable0 s" by (simp add:ReachStates_def)
    hence "reachable s0 s" by (simp add:reachable0_def)
    hence "\<exists>ts \<in> execution. ts ! 0 = s0 \<and> last ts = s" by (simp add:reachable_def)
    then obtain ts where a1: "ts \<in> execution" and a2: "ts ! 0 = s0" and a3: "last ts = s" by auto
    hence "s \<in> inv_good_tree" using inv_good_tree_lm_helper inv_good_tree_s0
    by (metis append_butlast_last_id exec_not_empty length_append_singleton lessI nth_append_length)
  }
  then show ?thesis by auto
qed

subsection \<open>def and proof of inv_block_free\<close>

inductive block_free :: "Block \<Rightarrow> bool"
  where f1: "get_leaf (Leaf a) \<Longrightarrow> block_free (Leaf a)" |
        f2: "block_free ll \<and> block_free lr \<and> block_free rl \<and> block_free rr \<and>
            \<not> (\<exists>la lb lc ld xa xb xc xd. (Node ll lr rl rr) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))
            \<Longrightarrow> block_free (Node ll lr rl rr)"

inductive_cases block_free_leaf_node:
  "block_free (Leaf a)"
  "block_free (Node ll lr rl rr)"

definition "pool_free_valid zerolevel \<equiv> (\<forall>b \<in> set zerolevel. block_free b)"

definition "inv_block_free \<equiv> {s::State. (\<forall>p \<in> set (pools s). pool_free_valid (zerolevelblocklist p))}"

lemma inv_free_s0: "s0 \<in> inv_block_free"
  unfolding s0_def inv_block_free_def pool_free_valid_def using s0_def poolsinit by auto

lemma inv_free_time_tick: "s \<in> inv_block_free \<Longrightarrow> time_tick s \<in> inv_block_free"
  unfolding time_tick_def Let_def inv_block_free_def pool_free_valid_def by auto
         
lemma inv_free_schedule: "s \<in> inv_block_free \<Longrightarrow> schedule s \<in> inv_block_free"
  unfolding schedule_def Let_def inv_block_free_def pool_free_valid_def 
  by (simp add: option.case_eq_if)

lemma all_leaf_free_tree: "\<forall>a \<in> set bli. get_leaf a \<Longrightarrow>
                 \<forall>b \<in> set (fst (pool_init bli idl ids num)). get_leaf b"
proof(induct "num" arbitrary: bli idl ids)
  case 0
  thus ?case by auto
next
  case (Suc n)
  obtain p where "pool_init bli idl ids (Suc n) = pool_init (bli@[Leaf(0, FREE, p)]) (idl\<union>{p}) (ids\<union>{p}) n"
    using pool_init_n[of "bli" "idl" ids n] by auto
  also have "\<forall>a \<in> set (bli@[Leaf(0, FREE, p)]). get_leaf a"
    using Suc(2) by auto
  ultimately show ?case using Suc.hyps by metis
qed

lemma all_leaf_empty_free_tree: "\<forall>b \<in> set (fst (pool_init [] {} ids num)). get_leaf b"
proof-
  have "\<forall>a \<in> set []. get_leaf a" by auto
  thus ?thesis using all_leaf_free_tree[of "[]" "{}" ids num]
    using all_leaf_free_tree by blast 
qed

lemma inv_free_k_mem_pool_define: "s \<in> inv_block_free \<Longrightarrow> fst (K_MEM_POOL_DEFINE s nam nlv num) \<in> inv_block_free"
proof -
  assume "s \<in> inv_block_free"
  hence p0: "\<forall>p. p \<in> set (pools s) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). block_free b)" 
    unfolding inv_block_free_def pool_free_valid_def by auto
  let ?t = "fst (K_MEM_POOL_DEFINE s nam nlv num)"
  {
    have p1: "butlast (pools ?t) = pools s" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    with p0 have p2: "\<forall>p. p \<in> set (butlast (pools ?t)) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). block_free b)" by auto
    moreover
    have p3: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). get_leaf b"
      unfolding K_MEM_POOL_DEFINE_def Let_def using all_leaf_empty_free_tree by auto
    from p3 have p4: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). block_free b"
      by (metis f1 get_leaf.simps(1) get_leaf.simps(2) tree.exhaust) 
    moreover
    have p5: "pools ?t = append (butlast (pools ?t)) [(last (pools ?t))]" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    with p2 p4 have "\<forall>p. p \<in> set (pools ?t) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). block_free b)"
      by (smt butlast.simps(2) butlast_append in_set_butlastD in_set_conv_decomp_last last.simps last_appendR list.distinct(1))  
  }
  then show ?thesis unfolding inv_block_free_def 
    by (simp add: pool_free_valid_def) 
qed

lemma block_free_alloc_leaf_case1:
  "lv < curl \<Longrightarrow>
  block_free (Leaf x) \<Longrightarrow>
  block_free (fst (alloc (Leaf x) li lv ids curl))"
  by auto

lemma block_free_alloc_leaf_case2:
  "\<not> lv < curl \<Longrightarrow>
  lv = curl \<Longrightarrow>
  block_free (Leaf x) \<Longrightarrow>
  block_free (fst (alloc (Leaf x) li lv ids curl))"
  apply auto
  by (simp add: f1)
  
lemma block_free_alloc_leaf_case3:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) = ALLOC \<Longrightarrow>
  block_free (Leaf x) \<Longrightarrow>
  block_free (fst (alloc (Leaf x) li lv ids curl))"
  by auto

lemma block_free_alloc_leaf_case4:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  block_free (Leaf x) \<Longrightarrow>
  block_free (fst (alloc (Leaf x) li lv ids curl))"
proof(induct "lv - curl" arbitrary: curl x li ids)
  case 0
  then show ?case by linarith 
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and pll_alloc: "fst (snd ll) \<noteq> ALLOC"
      and pll_free: "fst (snd ll) = FREE"
      and plr_free: "fst (snd lr) = FREE"
      and prl_free: "fst (snd rl) = FREE"
      and prr_free: "fst (snd rr) = FREE"
    unfolding divide_def Let_def by auto
  have free_ll: "block_free (Leaf ll)" by (simp add: f1) 
  have free_lr: "block_free (Leaf lr)" by (simp add: f1) 
  have free_rl: "block_free (Leaf rl)" by (simp add: f1) 
  have free_rr: "block_free (Leaf rr)" by (simp add: f1) 
  let ?li = "fst (snd (divide (Leaf x) li ids))"
  let ?ids = "snd (snd (divide (Leaf x) li ids))"
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_curl: "\<not> lv < curl" using lv_suc_curl by auto
    have de_lv_eq_curl: "\<not> lv = curl" using lv_suc_curl by auto
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto
    have step1: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h de_lv_less_curl de_lv_eq_curl Suc(5) pdivide by auto
    have ll_alloc: "fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)) = Leaf (fst ll, ALLOC, snd (snd ll))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free by auto
    have block_free_ll_alloc: "block_free (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)))"
      using ll_alloc by (simp add: f1)
    have no_four_free: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
      using ll_alloc plr_free prl_free prr_free by simp 
    have block_free_x_alloc: "block_free (fst (alloc (Leaf x) li lv ids curl))"
      using step1 block_free_ll_alloc free_lr free_rl free_rr no_four_free by (simp add: f2)
    then have ?case by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(3,4) by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have step2: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h Suc(3,4,5) pdivide by auto
    obtain b1 b2 b3 b4
      where ll_divide: "fst (divide (Leaf ll) ?li ?ids) = Node (Leaf b1) (Leaf b2) (Leaf b3) (Leaf b4)"
      unfolding divide_def Let_def by auto
    have block_free_ll_alloc: "block_free (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl de_lv_less_suc_curl de_lv_suc_curl pll_alloc free_ll by auto
    have ll_node: "get_leaf (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) = False"
      using inv_alloc_leaf_h de_lv_less_suc_curl de_lv_suc_curl pll_alloc ll_divide by auto
    have no_four_free_leaf: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
      using ll_node plr_free prl_free prr_free get_leaf.simps by auto
    have block_free_x_alloc: "block_free (fst (alloc (Leaf x) li lv ids curl))"
      using step2 block_free_ll_alloc free_lr free_rl free_rr no_four_free_leaf by (simp add: f2)
    then have ?case by auto
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma block_free_alloc_node_h1:
  "block_free b \<Longrightarrow>
  lv = curl \<Longrightarrow>
  block_free (fst (alloc b li lv ids curl))"
proof(induct b)
  case (Leaf x)
  then show ?case using block_free_alloc_leaf_case2 by auto
next
  case (Node b1 b2 b3 b4)
  have good_node: "block_free (Node b1 b2 b3 b4)" by (simp add: Node.prems(1)) 
  assume a0: "lv = curl"
  have lv_le_suc_curl: "lv < Suc curl" using a0 by auto
  have "block_free (fst (alloc (Node b1 b2 b3 b4) li lv ids curl))"
    using alloc.simps(2) lv_le_suc_curl good_node by auto
  then show ?case by auto
qed

lemma block_free_alloc_node_h2:
  "lv = curl \<Longrightarrow>
  fst (alloc (Leaf x) li lv ids curl) = Leaf (fst x, ALLOC, snd (snd x))"
proof-
  assume a0: "lv = curl"
  {assume b0: "fst (snd x) = FREE"
    have "fst (alloc (Leaf x) li lv ids curl) = Leaf (fst x, ALLOC, snd (snd x))"
      using alloc.simps(1) a0 b0 by auto
    then have ?thesis by auto
  }
  moreover
  {assume c0: "fst (snd x) = ALLOC"
    have "fst (alloc (Leaf x) li lv ids curl) = Leaf x"
      using alloc.simps(1) a0 c0 by auto
    then have ?thesis using c0 by (metis prod.exhaust_sel)
  }
  ultimately have ?thesis
    using block_state_type.exhaust by blast 
  then show ?thesis by auto
qed

lemma block_free_alloc_node_h3:
  "lv = curl \<Longrightarrow>
  fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
proof-
  assume a0: "lv = curl"
  have lv_le_suc_curl: "lv < Suc curl" using a0 by auto
  then show ?thesis using alloc.simps(2) lv_le_suc_curl by auto
qed

lemma block_free_alloc_node_h4:
  "\<not> lv < Suc curl \<Longrightarrow>
  get_leaf (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) = False"
proof-
  assume de_lv_le_suc_curl: "\<not> lv < Suc curl"
  {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b1: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    then have ?thesis using get_leaf.simps by auto
  }moreover
  {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b2: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    then have ?thesis using get_leaf.simps by auto
  }moreover
  {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b3: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    then have ?thesis using get_leaf.simps by auto
  }moreover
  {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b4: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    then have ?thesis using get_leaf.simps by auto
  }moreover
  {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have step5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    then have ?thesis using get_leaf.simps by auto
  }
  ultimately have ?thesis by blast
  then show ?thesis by auto
qed

lemma block_free_alloc_node:
  "block_free (Node b1 b2 b3 b4) \<Longrightarrow>
  \<not> lv < Suc curl \<Longrightarrow>
  block_free (fst (alloc (Node b1 b2 b3 b4) li lv ids curl))"
proof(induct "lv - curl" arbitrary: curl b1 b2 b3 b4 li ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have block_free_b1: "block_free b1"
    using Suc(3) block_free_leaf_node(2) by blast 
  have block_free_b2: "block_free b2"
    using Suc(3) block_free_leaf_node(2) by blast 
  have block_free_b3: "block_free b3"
    using Suc(3) block_free_leaf_node(2) by blast 
  have block_free_b4: "block_free b4"
    using Suc(3) block_free_leaf_node(2) by blast
  have no_four_free: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    using Suc(3) block_free_leaf_node(2) by blast 
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b1: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    have block_free_alloc_b1: "block_free (fst (alloc b1 li lv ids (Suc curl)))"
      using block_free_alloc_node_h1 block_free_b1 lv_suc_curl by auto
    have no_four_free_c1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
          using block_free_alloc_node_h2 lv_suc_curl by auto
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = Node m1 m2 m3 m4"
          using block_free_alloc_node_h3 lv_suc_curl by auto
        then have ?thesis using c21 by simp
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b1: "block_free (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4)"
      using block_free_alloc_b1 block_free_b2 block_free_b3 block_free_b4 no_four_free_c1 by (simp add: f2)
    have ?case using alloc_b1 block_free_b1 by auto
    }moreover
    {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b2: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    have block_free_alloc_b2: "block_free (fst (alloc b2 li lv ids (Suc curl)))"
      using block_free_alloc_node_h1 block_free_b2 lv_suc_curl by auto
    have no_four_free_c2: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
          using block_free_alloc_node_h2 lv_suc_curl by auto
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = Node m1 m2 m3 m4"
          using block_free_alloc_node_h3 lv_suc_curl by auto
        then have ?thesis using c21 by simp
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b2: "block_free (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4)"
      using block_free_alloc_b2 block_free_b1 block_free_b3 block_free_b4 no_four_free_c2 by (simp add: f2)
    have ?case using alloc_b2 block_free_b2 by auto
    }moreover
    {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b3: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    have block_free_alloc_b3: "block_free (fst (alloc b3 li lv ids (Suc curl)))"
      using block_free_alloc_node_h1 block_free_b3 lv_suc_curl by auto
    have no_four_free_c3: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
          using block_free_alloc_node_h2 lv_suc_curl by auto
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = Node m1 m2 m3 m4"
          using block_free_alloc_node_h3 lv_suc_curl by auto
        then have ?thesis using c21 by simp
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b3: "block_free (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4)"
      using block_free_alloc_b3 block_free_b1 block_free_b2 block_free_b4 no_four_free_c3 by (simp add: f2)
    have ?case using alloc_b3 block_free_b3 by auto
    }moreover
    {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b4: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    have block_free_alloc_b4: "block_free (fst (alloc b4 li lv ids (Suc curl)))"
      using block_free_alloc_node_h1 block_free_b4 lv_suc_curl by auto
    have no_four_free_c4: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
          using block_free_alloc_node_h2 lv_suc_curl by auto
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = Node m1 m2 m3 m4"
          using block_free_alloc_node_h3 lv_suc_curl by auto
        then have ?thesis using c21 by simp
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b4: "block_free (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl))))"
      using block_free_alloc_b4 block_free_b1 block_free_b2 block_free_b3 no_four_free_c4 by (simp add: f2)
    have ?case using alloc_b4 block_free_b4 by auto
    }moreover
    {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have step5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    then have ?case using Suc(3) by auto
    }
    ultimately have ?case by blast
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_le_suc_suc_curl: "\<not> lv < Suc (Suc curl)" using xa_gr_1 xa_lv_suc_curl by auto
    have lv_gr_suc_curl: "lv > Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_gr_suc_curl by auto
    have de_lv_eq_suc_curl: "lv \<noteq> Suc curl" using lv_gr_suc_curl by auto

    {assume c11: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b11: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using Suc(4) c11 by auto
    have block_free_b11: "block_free (fst (alloc b1 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl block_free_b1 de_lv_le_suc_suc_curl
      by (metis (full_types) block_free_alloc_leaf_case1 block_free_alloc_leaf_case3 block_free_alloc_leaf_case4 lessI tree.exhaust)
    have no_four_free_c11: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume c12: "fst (snd x) = ALLOC"
          have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf x"
            using alloc.simps(1) lv_gr_suc_curl c12 by auto
          then have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
            using c12 by (metis prod.exhaust_sel)
          then have ?thesis using c11 by simp
        }moreover
        {assume c13: "fst (snd x) \<noteq> ALLOC"
          obtain m1 m2 m3 m4 where x_divide: "fst (divide (Leaf x) li ids) = Node (Leaf m1) (Leaf m2) (Leaf m3) (Leaf m4)"
            unfolding divide_def Let_def by auto
          let ?li = "fst (snd (divide (Leaf x) li ids))"
          let ?ids = "snd (snd (divide (Leaf x) li ids))"
          have alloc_b1_node: "fst (alloc (Leaf x) li lv ids (Suc curl)) = Node (fst (alloc (Leaf m1) ?li lv ?ids (Suc (Suc curl)))) (Leaf m2) (Leaf m3) (Leaf m4)"
            using inv_alloc_leaf_h de_lv_le_suc_curl de_lv_eq_suc_curl c13 x_divide by auto
          have "get_leaf (fst (alloc (Leaf x) li lv ids (Suc curl))) = False" using alloc_b1_node by auto
          then have ?thesis using c11 get_leaf.simps by auto
        }
        ultimately have ?thesis by blast
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain n1 n2 n3 n4 where node_b1: "b1 = Node n1 n2 n3 n4" using c20 get_leaf.simps by (metis is_Leaf_def tree.collapse(2)) 
        have "get_leaf (fst (alloc b1 li lv ids (Suc curl))) = False"
          using block_free_alloc_node_h4 de_lv_le_suc_suc_curl node_b1 by auto
        then have ?thesis using get_leaf.simps by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b11: "block_free (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4)"
      using block_free_b11 block_free_b2 block_free_b3 block_free_b4 no_four_free_c11 by (simp add: f2)
    have ?case using alloc_b11 block_free_b11 by auto
    }moreover
    {assume c22: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b22: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using Suc(4) c22 by auto
    have block_free_b22: "block_free (fst (alloc b2 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl block_free_b2 de_lv_le_suc_suc_curl
      by (metis (full_types) block_free_alloc_leaf_case1 block_free_alloc_leaf_case3 block_free_alloc_leaf_case4 lessI tree.exhaust)
    have no_four_free_c22: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume c12: "fst (snd x) = ALLOC"
          have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf x"
            using alloc.simps(1) lv_gr_suc_curl c12 by auto
          then have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
            using c12 by (metis prod.exhaust_sel)
          then have ?thesis using c11 by simp
        }moreover
        {assume c13: "fst (snd x) \<noteq> ALLOC"
          obtain m1 m2 m3 m4 where x_divide: "fst (divide (Leaf x) li ids) = Node (Leaf m1) (Leaf m2) (Leaf m3) (Leaf m4)"
            unfolding divide_def Let_def by auto
          let ?li = "fst (snd (divide (Leaf x) li ids))"
          let ?ids = "snd (snd (divide (Leaf x) li ids))"
          have alloc_b1_node: "fst (alloc (Leaf x) li lv ids (Suc curl)) = Node (fst (alloc (Leaf m1) ?li lv ?ids (Suc (Suc curl)))) (Leaf m2) (Leaf m3) (Leaf m4)"
            using inv_alloc_leaf_h de_lv_le_suc_curl de_lv_eq_suc_curl c13 x_divide by auto
          have "get_leaf (fst (alloc (Leaf x) li lv ids (Suc curl))) = False" using alloc_b1_node by auto
          then have ?thesis using c11 get_leaf.simps by auto
        }
        ultimately have ?thesis by blast
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain n1 n2 n3 n4 where node_b1: "b2 = Node n1 n2 n3 n4" using c20 get_leaf.simps by (metis is_Leaf_def tree.collapse(2)) 
        have "get_leaf (fst (alloc b2 li lv ids (Suc curl))) = False"
          using block_free_alloc_node_h4 de_lv_le_suc_suc_curl node_b1 by auto
        then have ?thesis using get_leaf.simps by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b22: "block_free (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4)"
      using block_free_b22 block_free_b1 block_free_b3 block_free_b4 no_four_free_c22 by (simp add: f2)
    have ?case using alloc_b22 block_free_b22 by auto
    }moreover
    {assume c33: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b33: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using Suc(4) c33 by auto
    have block_free_b33: "block_free (fst (alloc b3 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl block_free_b3 de_lv_le_suc_suc_curl
      by (metis (full_types) block_free_alloc_leaf_case1 block_free_alloc_leaf_case3 block_free_alloc_leaf_case4 lessI tree.exhaust)
    have no_four_free_c33: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume c12: "fst (snd x) = ALLOC"
          have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf x"
            using alloc.simps(1) lv_gr_suc_curl c12 by auto
          then have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
            using c12 by (metis prod.exhaust_sel)
          then have ?thesis using c11 by simp
        }moreover
        {assume c13: "fst (snd x) \<noteq> ALLOC"
          obtain m1 m2 m3 m4 where x_divide: "fst (divide (Leaf x) li ids) = Node (Leaf m1) (Leaf m2) (Leaf m3) (Leaf m4)"
            unfolding divide_def Let_def by auto
          let ?li = "fst (snd (divide (Leaf x) li ids))"
          let ?ids = "snd (snd (divide (Leaf x) li ids))"
          have alloc_b1_node: "fst (alloc (Leaf x) li lv ids (Suc curl)) = Node (fst (alloc (Leaf m1) ?li lv ?ids (Suc (Suc curl)))) (Leaf m2) (Leaf m3) (Leaf m4)"
            using inv_alloc_leaf_h de_lv_le_suc_curl de_lv_eq_suc_curl c13 x_divide by auto
          have "get_leaf (fst (alloc (Leaf x) li lv ids (Suc curl))) = False" using alloc_b1_node by auto
          then have ?thesis using c11 get_leaf.simps by auto
        }
        ultimately have ?thesis by blast
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain n1 n2 n3 n4 where node_b1: "b3 = Node n1 n2 n3 n4" using c20 get_leaf.simps by (metis is_Leaf_def tree.collapse(2)) 
        have "get_leaf (fst (alloc b3 li lv ids (Suc curl))) = False"
          using block_free_alloc_node_h4 de_lv_le_suc_suc_curl node_b1 by auto
        then have ?thesis using get_leaf.simps by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b33: "block_free (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4)"
      using block_free_b33 block_free_b1 block_free_b2 block_free_b4 no_four_free_c33 by (simp add: f2)
    have ?case using alloc_b33 block_free_b33 by auto
    }moreover
    {assume c44: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                  snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b44: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using Suc(4) c44 by auto
    have block_free_b44: "block_free (fst (alloc b4 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl block_free_b4 de_lv_le_suc_suc_curl
      by (metis (full_types) block_free_alloc_leaf_case1 block_free_alloc_leaf_case3 block_free_alloc_leaf_case4 lessI tree.exhaust)
    have no_four_free_c44: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume c12: "fst (snd x) = ALLOC"
          have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf x"
            using alloc.simps(1) lv_gr_suc_curl c12 by auto
          then have "fst (alloc (Leaf x) li lv ids (Suc curl)) = Leaf (fst x, ALLOC, snd (snd x))"
            using c12 by (metis prod.exhaust_sel)
          then have ?thesis using c11 by simp
        }moreover
        {assume c13: "fst (snd x) \<noteq> ALLOC"
          obtain m1 m2 m3 m4 where x_divide: "fst (divide (Leaf x) li ids) = Node (Leaf m1) (Leaf m2) (Leaf m3) (Leaf m4)"
            unfolding divide_def Let_def by auto
          let ?li = "fst (snd (divide (Leaf x) li ids))"
          let ?ids = "snd (snd (divide (Leaf x) li ids))"
          have alloc_b1_node: "fst (alloc (Leaf x) li lv ids (Suc curl)) = Node (fst (alloc (Leaf m1) ?li lv ?ids (Suc (Suc curl)))) (Leaf m2) (Leaf m3) (Leaf m4)"
            using inv_alloc_leaf_h de_lv_le_suc_curl de_lv_eq_suc_curl c13 x_divide by auto
          have "get_leaf (fst (alloc (Leaf x) li lv ids (Suc curl))) = False" using alloc_b1_node by auto
          then have ?thesis using c11 get_leaf.simps by auto
        }
        ultimately have ?thesis by blast
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain n1 n2 n3 n4 where node_b1: "b4 = Node n1 n2 n3 n4" using c20 get_leaf.simps by (metis is_Leaf_def tree.collapse(2)) 
        have "get_leaf (fst (alloc b4 li lv ids (Suc curl))) = False"
          using block_free_alloc_node_h4 de_lv_le_suc_suc_curl node_b1 by auto
        then have ?thesis using get_leaf.simps by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_free_b44: "block_free (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl))))"
      using block_free_b44 block_free_b1 block_free_b2 block_free_b3 no_four_free_c44 by (simp add: f2)
    have ?case using alloc_b44 block_free_b44 by auto
    }moreover
    {assume c55: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have step5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    then have ?case using Suc(3) by auto
    }
    ultimately have ?case by blast
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma inv_block_free_alloc:
  "block_free b \<Longrightarrow>
  snd (snd (snd (alloc b li lv ids curl))) = True \<Longrightarrow>
  block_free (fst (alloc b li lv ids curl))"
proof(induct b)
  case (Leaf x)
  then show ?case using block_free_alloc_leaf_case1 block_free_alloc_leaf_case2 block_free_alloc_leaf_case3 block_free_alloc_leaf_case4
    by simp
next
  case (Node b1 b2 b3 b4)
  then show ?case using block_free_alloc_node by auto
qed

lemma pool_alloc_block_free_case1:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
proof-
  assume a0: "pool_free_valid (zerolevelblocklist po)"
     and a1: "\<not> lv < 0"
     and a2: "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). block_free b" using a0 pool_free_valid_def by auto
  have p1: "block_free (zerolevelblocklist po ! n)" using p0 a2 by auto
  have p2: "block_free (fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))" using p1 a2 inv_block_free_alloc by auto
  let ?po = "let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! n) (freelist po) lv ids 0
            in po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>"
  {
    have p3: "fst (pool_alloc po lv n ids) = ?po" apply simp using a2 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist ?po ! n) = fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)" unfolding Let_def using a2 by auto
    then have p5: "block_free (zerolevelblocklist ?po ! n)" using p2 unfolding Let_def by auto
    with p0 have p6: "\<forall>b \<in> set (zerolevelblocklist ?po). block_free b" unfolding Let_def apply auto
      by (metis in_set_conv_nth length_list_update nth_list_update_neq p0)
    have p7: "pool_free_valid (zerolevelblocklist ?po)" unfolding pool_free_valid_def using p6 by auto
    with p3 have p8: "pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_alloc_block_free_case3:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
  by auto

lemma pool_alloc_block_free_case2:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith
next
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto
  have step: "pool_alloc po lv n ids = pool_alloc po lv (Suc n) ids" using Suc by auto
  { 
    assume a00: "snd (snd (snd (alloc ((zerolevelblocklist po) ! (Suc n)) (freelist po) lv ids 0))) = False \<and> (Suc n) < length (zerolevelblocklist po) - 1"
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith  
    ultimately have "pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv (Suc n) ids)))"
      using Suc.hyps(1) Suc.prems(1) by blast
  }
  moreover
  have "pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv (Suc n) ids)))"
    using Suc.prems(1) pool_alloc_block_free_case1 pool_alloc_block_free_case3 calculation by blast    
  ultimately show ?case using step by auto
qed

lemma inv_block_free_pool_alloc:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
  pool_free_valid (zerolevelblocklist (fst (pool_alloc po lv n ids)))"
  apply(cases "lv < 0") apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)")
  using pool_alloc_block_free_case1[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_alloc_block_free_case3[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  using pool_alloc_block_free_case2[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] by simp

lemma inv_block_free_k_mem_pool_alloc_helper1:
  "s \<in> inv_block_free \<and> po \<in> set (pools s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_block_free"
proof-
  assume a0: "s \<in> inv_block_free \<and> po \<in> set (pools s)"
  hence p0: "\<forall>p \<in> set (pools s). pool_free_valid (zerolevelblocklist p)"
    by (simp add: inv_block_free_def)
  hence p1: "pool_free_valid (zerolevelblocklist po)"
    by (simp add: a0)
  let ?rpi = "pool_alloc po lv 0 (idset s)"
  have p2: "pool_free_valid (zerolevelblocklist (fst ?rpi))" using inv_block_free_pool_alloc p1 by blast
  moreover
  have p3: "\<forall>p \<in> set ((remove1 po (pools s)) @ [fst ?rpi]). pool_free_valid (zerolevelblocklist p)" using p0 p2 by auto
  let ?s = "s\<lparr>pools := remove1 po (pools s) @ [fst ?rpi], idset := fst (snd ?rpi)\<rparr>"
  have p4: "?s \<in> inv_block_free"
    unfolding inv_block_free_def using p3 by auto
  then show "s \<in> inv_block_free \<and> po \<in> set (pools s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_block_free"
    by (smt fst_conv)
qed

lemma inv_block_free_k_mem_pool_alloc_helper3:
  "s \<in> inv_block_free \<Longrightarrow>
    \<not> snd (snd (let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! 0) (freelist po) lv (idset s) 0; re = snd (snd (snd aa))
                 in if re \<and> zeroli \<noteq> [] then (po\<lparr>zerolevelblocklist := zeroli[0 := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)
                    else if re = False \<and> 0 < length zeroli - 1 then pool_alloc po lv (Suc 0) (idset s) else (po, idset s, False))) \<Longrightarrow>
    schedule (case cur s of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> name po)\<rparr>)) \<in> inv_block_free"
proof-
  assume "s \<in> inv_block_free"
  hence p0: "\<forall>p \<in> set (pools s). pool_free_valid (zerolevelblocklist p)"
    using inv_block_free_def by blast
  let ?t = "case (cur s) of None \<Rightarrow> s
                    | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := (waitq s)(th \<mapsto> name po)\<rparr>)"
  {
    have p1: "pools s = pools ?t" by (simp add: option.case_eq_if)
    with p0 have p2: "\<forall>p \<in> set (pools ?t). pool_free_valid (zerolevelblocklist p)" by simp
    from p2 have p3: "?t \<in> inv_block_free"
      by (simp add: inv_block_free_def)
    from p3 have p4: "schedule ?t \<in> inv_block_free" by (simp add:inv_free_schedule)
  }
  then show ?thesis by blast
qed
    
lemma inv_block_free_k_mem_pool_alloc_helper2:
  "s \<in> inv_block_free \<and> po \<in> set (pools s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) \<noteq> True \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_block_free"
  apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
   prefer 2
   apply blast
  apply(simp add:inv_free_schedule)
  using inv_block_free_k_mem_pool_alloc_helper3 by blast
    
lemma inv_free_k_mem_pool_alloc: "s \<in> inv_block_free \<and> po \<in> set (pools s) \<Longrightarrow> fst (k_mem_pool_alloc s po lv ti) \<in> inv_block_free" 
proof (induct ti)
  case WAIT
  then show ?case unfolding k_mem_pool_alloc_def
    apply(case_tac "lv < 0")
     apply(simp add:Let_def)
    apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = True")
       apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
      apply(simp add:Let_def)
    using inv_block_free_k_mem_pool_alloc_helper1 inv_block_free_k_mem_pool_alloc_helper2 snd_conv
      unfolding Let_def by simp+
  case FOREVER
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_block_free\<close> k_mem_pool_alloc_def option.case_eq_if)
  case NO_WAIT
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(2) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_block_free\<close> fst_conv k_mem_pool_alloc_def timeout_state_type.distinct(1) timeout_state_type.distinct(5))
qed

lemma block_free_combine:
  "b = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)) \<Longrightarrow>
  block_free (fst (combine b li ids))"
  unfolding combine_def Let_def
  by (simp add: f1)

lemma inv_block_free_free:
  "block_free b \<Longrightarrow>
  snd (snd (snd (free b li num ids))) = True \<Longrightarrow>
  block_free (fst (free b li num ids))"
proof(induct b)
  case (Leaf x)
  then show ?case
    apply auto
    by (simp add: f1)
next
  case (Node b1 b2 b3 b4)
  have free_b1: "block_free b1"
    using Node.prems(1) block_free_leaf_node(2) by blast
  have free_b2: "block_free b2"
    using Node.prems(1) block_free_leaf_node(2) by blast
  have free_b3: "block_free b3"
    using Node.prems(1) block_free_leaf_node(2) by blast
  have free_b4: "block_free b4"
    using Node.prems(1) block_free_leaf_node(2) by blast
  have no_four_free: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 b4) = (Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))))"
    using Node.prems(1) block_free_leaf_node(2) by blast

  {assume c1: "snd (snd (snd (free b1 li num ids)))"
    let ?c1 = "free b1 li num ids"
    let ?step1 = "if (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node (fst ?c1) b2 b3 b4, fst (snd ?c1), (fst (snd (snd ?c1))), True)"
    have step1: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step1"
      unfolding free.simps(2) Let_def using c1 by auto
    have good_free_b1: "block_free (fst ?c1)"
      using free_b1 c1 Node.hyps(1) by auto
    have "block_free (fst ?step1)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step1 = fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        then have ?thesis using block_free_combine step_case0 by simp
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step1 = Node (fst ?c1) b2 b3 b4"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using good_free_b1 free_b2 free_b3 free_b4 case1 by (simp add: f2)
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step1 by auto
  }moreover
  {assume c2: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids)))"
    let ?c2 = "free b2 li num ids"
    let ?step2 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 (fst ?c2) b3 b4, fst (snd ?c2), (fst (snd (snd ?c2))), True)"
    have step2: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step2"
      unfolding free.simps(2) Let_def using c2 by auto
    have good_free_b2: "block_free (fst ?c2)"
      using free_b2 c2 Node.hyps(2) by auto
    have "block_free (fst ?step2)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step2 = fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        then have ?thesis using block_free_combine step_case0 by simp
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step2 = Node b1 (fst ?c2) b3 b4"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using good_free_b2 free_b1 free_b3 free_b4 case1 by (simp add: f2)
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step2 by auto
  }moreover
  {assume c3: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids)))"
    let ?c3 = "free b3 li num ids"
    let ?step3 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 (fst ?c3) b4, fst (snd ?c3), (fst (snd (snd ?c3))), True)"
    have step3: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step3"
      unfolding free.simps(2) Let_def using c3 by auto
    have good_free_b3: "block_free (fst ?c3)"
      using free_b3 c3 Node.hyps(3) by auto
    have "block_free (fst ?step3)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step3 = fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        then have ?thesis using block_free_combine step_case0 by simp
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step3 = Node b1 b2 (fst ?c3) b4"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using good_free_b3 free_b1 free_b2 free_b4 case1 by (simp add: f2)
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step3 by auto
  }moreover
  {assume c4: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids)))"
    let ?c4 = "free b4 li num ids"
    let ?step4 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 b3 (fst ?c4), fst (snd ?c4), (fst (snd (snd ?c4))), True)"
    have step4: "fst (free (Node b1 b2 b3 b4) li num ids) = fst ?step4"
      unfolding free.simps(2) Let_def using c4 by auto
    have good_free_b4: "block_free (fst ?c4)"
      using free_b4 c4 Node.hyps(4) by auto
    have "block_free (fst ?step4)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step4 = fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        then have ?thesis using block_free_combine step_case0 by simp
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step4 = Node b1 b2 b3 (fst ?c4)"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using good_free_b4 free_b1 free_b2 free_b3 case1 by (simp add: f2)
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step4 by auto
  }moreover
  {assume c5: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids))) = False"
    have step5: "fst (free (Node b1 b2 b3 b4) li num ids) = (Node b1 b2 b3 b4)"
      unfolding free.simps(2) Let_def using c5 by auto
    then have ?case using Node.prems(1) by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma pool_free_block_free_case1:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  pool_free_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
proof-
  assume a0: "pool_free_valid (zerolevelblocklist po)"
     and a1: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). block_free b" using a0 pool_free_valid_def by auto
  have p1: "block_free (zerolevelblocklist po ! n)" using p0 a1 by auto
  have p2: "block_free (fst (free (zerolevelblocklist po ! n) (freelist po) num ids))" using p1 a1 inv_block_free_free by auto
  let ?po = "let zeroli = zerolevelblocklist po; aa = free (zeroli ! n) (freelist po) num ids
            in po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>"
  {
    have p3: "fst (pool_free po num n ids) = ?po" apply simp using a1 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist ?po ! n) = fst (free (zerolevelblocklist po ! n) (freelist po) num ids)" unfolding Let_def using a1 by auto
    then have p5: "block_free (zerolevelblocklist ?po ! n)" using p2 unfolding Let_def by auto
    with p0 have p6: "\<forall>b \<in> set (zerolevelblocklist ?po). block_free b" unfolding Let_def apply auto
      by (metis in_set_conv_nth length_list_update nth_list_update_neq p0)
    have p7: "pool_free_valid (zerolevelblocklist ?po)" unfolding pool_free_valid_def using p6 by auto
    with p3 have p8: "pool_free_valid (zerolevelblocklist (fst (pool_free po num n ids)))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_free_block_free_case3:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
    \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
    \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
    pool_free_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
  by auto

lemma pool_free_block_free_case2:
  "pool_free_valid (zerolevelblocklist po) \<Longrightarrow>
    snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
    pool_free_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith 
next 
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto     
  have step: "pool_free po num n ids = pool_free po num (Suc n) ids" using Suc by auto
  { 
    assume a00: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1) "
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith   
    ultimately have "pool_free_valid (zerolevelblocklist (fst (pool_free po num (Suc n) ids)))"
      using Suc.hyps(1) Suc.prems(1) pool_free_block_free_case1 pool_free_block_free_case3 by blast
  }    
  moreover 
  have "pool_free_valid (zerolevelblocklist (fst (pool_free po num (Suc n) ids)))"
    using Suc.prems(2) calculation by blast 
  ultimately show ?case using step by auto
qed

lemma inv_block_free_pool_free: "pool_free_valid (zerolevelblocklist po) \<Longrightarrow> pool_free_valid (zerolevelblocklist (fst (pool_free po num n ids)))"
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)")
  using pool_free_block_free_case1[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_free_block_free_case3[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  using pool_free_block_free_case2[where po = "po" and num = "num" and n = "n" and ids = "ids"] by simp

lemma inv_free_k_mem_pool_free: "po \<in> set (pools s) \<and> s \<in> inv_block_free \<Longrightarrow> fst (k_mem_pool_free s po num) \<in> inv_block_free" 
proof-
  assume a0: "po \<in> set (pools s) \<and> s \<in> inv_block_free"
  hence p0: "\<forall>p \<in> set (pools s). pool_free_valid (zerolevelblocklist p)" unfolding inv_block_free_def by auto
  from a0 p0 have p1: "pool_free_valid (zerolevelblocklist po)" by simp 
  let ?po1 = "fst (pool_free po num 0 (idset s))"
  from p1 have p2: "pool_free_valid (zerolevelblocklist ?po1)"
    using inv_block_free_pool_free[where po = "po" and num = "num" and n = 0 and ids = "idset s"] by auto
  let ?t = "fst (k_mem_pool_free s po num)"
  {
    have p3: "set (pools ?t) = set (append (remove1 po (pools s)) [?po1])"
      unfolding k_mem_pool_free_def
      apply(case_tac "snd (snd (pool_free po num 0 (idset s))) = True")
       apply(case_tac "{t. (waitq s) t = Some (name po)} \<noteq> {}")
        apply(simp add:Let_def)
       apply(simp add:Let_def)
      using inv_block_k_mem_pool_free_helper[of po num s]
      pool_free_lm[where po = "po" and num = "num" and n = 0 and ids = "idset s" and re="pool_free po num 0 (idset s)"]
      set_helper[of po "pools s"]
      snd_conv fst_conv a0 by simp
    fix pl
    assume a1: "pl \<in> set (pools ?t)" 
    have p4: "pool_free_valid (zerolevelblocklist pl)"
      proof(cases "pl = ?po1")
        assume "pl = ?po1"
        with p2 show ?thesis by simp
      next
        assume "pl \<noteq> ?po1"
        with p0 p3 a1 show ?thesis by force
      qed
  }
  then show ?thesis unfolding inv_block_free_def by force
qed
      
lemma inv_free_lm_helper: "\<forall>ts. (ts \<in> execution \<and> ts ! 0 \<in> inv_block_free \<longrightarrow> (\<forall>i<length ts. ts ! i \<in> inv_block_free))"
proof -
  {
    fix ts
    assume p0: "ts \<in> execution"
       and p1: "ts ! 0 \<in> inv_block_free"
    then have "\<forall>i<length ts. ts ! i \<in> inv_block_free"
      apply(induct ts)
       apply simp
      using inv_free_k_mem_pool_define inv_free_k_mem_pool_alloc inv_free_k_mem_pool_free inv_free_time_tick inv_free_schedule
      apply (metis One_nat_def Suc_less_eq Suc_pred length_Cons neq0_conv nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_free_k_mem_pool_alloc length_Cons neq0_conv nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_free_k_mem_pool_free length_Cons neq0_conv nth.simps nth_Cons')
      apply (metis One_nat_def Suc_less_eq Suc_pred inv_free_time_tick length_Cons neq0_conv nth_Cons')
      by (metis One_nat_def Suc_less_eq Suc_pred inv_free_schedule length_Cons neq0_conv nth_Cons')
  }
  then show ?thesis by auto
qed

lemma inv_free_lm: "ReachStates \<subseteq> inv_block_free"
proof -
  {
    fix s
    assume p0: "s \<in> ReachStates"
    hence "reachable0 s" by (simp add:ReachStates_def)
    hence "reachable s0 s" by (simp add:reachable0_def)
    hence "\<exists>ts \<in> execution. ts ! 0 = s0 \<and> last ts = s" by (simp add:reachable_def)
    then obtain ts where a1: "ts \<in> execution" and a2: "ts ! 0 = s0" and a3: "last ts = s" by auto
    hence "s \<in> inv_block_free" using inv_free_lm_helper inv_free_s0
    by (metis append_butlast_last_id exec_not_empty length_append_singleton lessI nth_append_length)
  }
  then show ?thesis by auto
qed

subsection \<open>def and proof of inv_ids\<close>

inductive id_ids:: "Block \<Rightarrow> ID set \<Rightarrow> bool"
  where i1: "snd (snd x) \<in> ids \<Longrightarrow> id_ids (Leaf x) ids" |
        i2: "id_ids ll ids \<and> id_ids lr ids \<and> id_ids rl ids \<and> id_ids rr ids \<Longrightarrow> id_ids (Node ll lr rl rr) ids"

inductive_cases id_ids_leaf_node:
  "id_ids (Leaf x) ids"
  "id_ids (Node ll lr rl rr) ids"

lemma id_ids_ext:
  assumes a0: "ids \<subseteq> ids'"
      and a1: "id_ids b ids"
    shows "id_ids b ids'"
  using a1
proof(induct b)
  case (Leaf x)
  have "\<forall>i. i \<in> ids' \<or> i \<notin> ids" by (metis a0 subsetCE)
  then show ?case
    by (metis (no_types) id_ids_leaf_node(1)[OF Leaf(1)] i1)
next
  case (Node b1 b2 b3 b4)
  have "id_ids b1 ids \<and>
        id_ids b2 ids \<and>
        id_ids b3 ids \<and>
        id_ids b4 ids"
    using id_ids_leaf_node(2)[OF Node(5)] by auto
  then show ?case using Node i2 by auto
qed

lemma idsets_block_id_ids:
  "id_ids b ids \<Longrightarrow>
  idsets_block b \<subseteq> ids"
proof(induct b)
  case (Leaf x)
  have leaf_belong: "snd (snd x) \<in> ids"
    using Leaf.prems id_ids_leaf_node(1) by blast
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have b1_belong: "id_ids b1 ids"
    using Node.prems id_ids_leaf_node(2) by blast
  have b2_belong: "id_ids b2 ids"
    using Node.prems id_ids_leaf_node(2) by blast
  have b3_belong: "id_ids b3 ids"
    using Node.prems id_ids_leaf_node(2) by blast
  have b4_belong: "id_ids b4 ids"
    using Node.prems id_ids_leaf_node(2) by blast
  have b1_subset: "idsets_block b1 \<subseteq> ids"
    using b1_belong Node.hyps(1) by auto
  have b2_subset: "idsets_block b2 \<subseteq> ids"
    using b2_belong Node.hyps(2) by auto
  have b3_subset: "idsets_block b3 \<subseteq> ids"
    using b3_belong Node.hyps(3) by auto
  have b4_subset: "idsets_block b4 \<subseteq> ids"
    using b4_belong Node.hyps(4) by auto
  show ?case using b1_subset b2_subset b3_subset b4_subset idsets_block.simps(2) by auto
qed

lemma idsets_block_id_ids2:
  "idsets_block b \<subseteq> ids \<Longrightarrow>
  id_ids b ids"
proof(induct b)
  case (Leaf x)
  have leaf_belong: "{snd (snd x)} \<subseteq> ids"
    using Leaf.prems by auto
  then show ?case using i1 by auto
next
  case (Node b1 b2 b3 b4)
  have b1_belong: "idsets_block b1 \<subseteq> ids"
    using Node.prems by simp
  have b2_belong: "idsets_block b2 \<subseteq> ids"
    using Node.prems by simp
  have b3_belong: "idsets_block b3 \<subseteq> ids"
    using Node.prems by simp
  have b4_belong: "idsets_block b4 \<subseteq> ids"
    using Node.prems by simp
  have b1_subset: "id_ids b1 ids"
    using b1_belong Node.hyps(1) by auto
  have b2_subset: "id_ids b2 ids"
    using b2_belong Node.hyps(2) by auto
  have b3_subset: "id_ids b3 ids"
    using b3_belong Node.hyps(3) by auto
  have b4_subset: "id_ids b4 ids"
    using b4_belong Node.hyps(4) by auto
  then show ?case using b1_subset b2_subset b3_subset b4_subset i2 by auto
qed

inductive diff_ids:: "Block \<Rightarrow> bool"
  where diff1: "diff_ids (Leaf a)" |
        diff2: "(idsets_block b1) \<inter> (idsets_block b2) = {} \<and> (idsets_block b1) \<inter> (idsets_block b3) = {} \<and> (idsets_block b1) \<inter> (idsets_block b4) = {} \<and>
                (idsets_block b2) \<inter> (idsets_block b3) = {} \<and> (idsets_block b2) \<inter> (idsets_block b4) = {} \<and>
                (idsets_block b3) \<inter> (idsets_block b4) = {} \<and>
                diff_ids b1 \<and> diff_ids b2 \<and> diff_ids b3 \<and> diff_ids b4
                \<Longrightarrow> diff_ids (Node b1 b2 b3 b4)"

inductive_cases diff_ids_leaf_node:
  "diff_ids (Leaf a)"
  "diff_ids (Node ll lr rl rr)"

definition "id_ids_valid p ids \<equiv> (\<forall>b\<in>set (zerolevelblocklist p). id_ids b ids)"

definition "diff_ids_valid p \<equiv> (\<forall>b\<in>set (zerolevelblocklist p). diff_ids b)"

definition "inv_ids \<equiv> {s::State. (\<forall>p \<in> set (pools s). id_ids_valid p (idset s) \<and> diff_ids_valid p)}"

lemma inv_ids_s0: "s0 \<in> inv_ids"
  unfolding s0_def inv_ids_def id_ids_valid_def diff_ids_valid_def using s0_def poolsinit by auto

lemma inv_ids_time_tick: "s \<in> inv_ids \<Longrightarrow> time_tick s \<in> inv_ids"
  unfolding time_tick_def Let_def inv_ids_def id_ids_valid_def diff_ids_valid_def by auto
         
lemma inv_ids_schedule: "s \<in> inv_ids \<Longrightarrow> schedule s \<in> inv_ids"
  unfolding schedule_def Let_def inv_ids_def id_ids_valid_def diff_ids_valid_def
  by (simp add: option.case_eq_if)

lemma all_leaf_ids_tree:
  "\<forall>a \<in> set bli. get_leaf a \<and> get_blockid a \<in> ids \<Longrightarrow>
   \<forall>b \<in> set (fst (pool_init bli idl ids num)). get_leaf b \<and> get_blockid b \<in> snd (snd (pool_init bli idl ids num))"
proof(induct "num" arbitrary: bli idl ids)
  case 0
  thus ?case by auto
next
  case (Suc n)
  obtain p where "pool_init bli idl ids (Suc n) = pool_init (bli@[Leaf(0, FREE, p)]) (idl\<union>{p}) (ids\<union>{p}) n"
    using pool_init_n[of "bli" "idl" ids n] by auto
  also have "\<forall>a \<in> set (bli@[Leaf(0, FREE, p)]). get_leaf a \<and> (get_blockid a) \<in> ids\<union>{p}"
    using Suc(2) get_blocklevel_def get_blocktype_def get_blockid_def by auto
  ultimately show ?case using Suc.hyps by presburger
qed

lemma all_leaf_empty_ids_tree: 
  "\<forall>b \<in> set (fst (pool_init [] {} ids num)). get_leaf b \<and> get_blockid b \<in> snd (snd (pool_init [] {} ids num))"
proof-
  have "\<forall>a \<in> set []. get_leaf a \<and> get_blockid a \<in> ids" by auto
  thus ?thesis using all_leaf_ids_tree[of "[]" "{}" ids num]
    using all_leaf_ids_tree by blast 
qed

lemma idset_subset_h:
  "x \<in> ids \<Longrightarrow>
  x \<in> snd (snd (pool_init bli idl ids num))"
proof(induct num arbitrary: bli idl ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have step: "pool_init bli idl ids (Suc xa) = pool_init (bli @ [Leaf(0, FREE, (fst (getnewid2 ids)))]) (idl \<union> {fst (getnewid2 ids)}) (snd (getnewid2 ids)) xa"
    using pool_init.simps by (smt diff_Suc_1 nat.simps(3))
  have p0: "x \<in> snd (getnewid2 ids)"
    using Suc(2) getnewid2_inc by auto
  have p1: "x \<in> snd (snd (pool_init (bli @ [Leaf(0, FREE, (fst (getnewid2 ids)))]) (idl \<union> {fst (getnewid2 ids)}) (snd (getnewid2 ids)) xa))"
    using Suc(1) p0 by blast
  then show ?case using step by auto
qed

lemma idset_subset:
  "idset s \<subseteq> idset (fst (K_MEM_POOL_DEFINE s nam nlv num))"
  unfolding K_MEM_POOL_DEFINE_def Let_def
  apply auto
  using idset_subset_h
  by (smt UnCI exists_p_getnewid2 snd_conv)

lemma inv_ids_k_mem_pool_define: "s \<in> inv_ids \<Longrightarrow> fst (K_MEM_POOL_DEFINE s nam nlv num) \<in> inv_ids"
proof-
  assume "s \<in> inv_ids"
  hence p0: "\<forall>p. p \<in> set (pools s) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). id_ids b (idset s) \<and> diff_ids b)"
    unfolding inv_ids_def id_ids_valid_def diff_ids_valid_def by auto
  let ?t = "fst (K_MEM_POOL_DEFINE s nam nlv num)"
  {
    have s_in_t: "idset s \<subseteq> idset ?t"
      by (simp add: idset_subset)
    have p1: "butlast (pools ?t) = pools s" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    have p2: "\<forall>p. p \<in> set (butlast (pools ?t)) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). id_ids b (idset ?t) \<and> diff_ids b)"
      using id_ids_ext p0 p1 s_in_t by auto
    moreover
    have p3: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). get_leaf b \<and> get_blockid b \<in> (idset ?t)"
      unfolding K_MEM_POOL_DEFINE_def Let_def using all_leaf_empty_ids_tree[where ids = "idset s" and num = "num"] by auto
    from p3 have p40: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). id_ids b (idset ?t)"
      using id_ids_leaf_node(1) get_leaf_def get_blockid_def
      proof -
      { fix tt :: "(nat \<times> block_state_type \<times> nat) tree"
        obtain pp :: "(nat \<times> block_state_type \<times> nat) tree \<Rightarrow> nat \<times> block_state_type \<times> nat" where
          ff1: "\<forall>t. Leaf (pp t) = t \<or> \<not> get_leaf t"
          by (metis get_leaf.simps(2) tree.exhaust)
        then have "\<forall>f fa t. (case t of Leaf x \<Rightarrow> fa x::nat | Node x xa xb xc \<Rightarrow> f x xa xb xc) = fa (pp t) \<or> \<not> get_leaf t"
          by (metis tree.simps(5))
        then have "tt \<notin> set (zerolevelblocklist (last (pools (fst (K_MEM_POOL_DEFINE s nam nlv num))))) \<or> id_ids tt (idset (fst (K_MEM_POOL_DEFINE s nam nlv num)))"
          using ff1 by (metis (no_types) get_blockid_def id_ids.intros(1) p3) }
        then show ?thesis by blast
      qed
    from p3 have p41: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). diff_ids b"
      using diff2 get_leaf_def
      by (metis diff1 get_leaf.simps(2) tree.exhaust)
    have p4: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). id_ids b (idset ?t) \<and> diff_ids b"
      using p40 p41 by auto
    moreover
    have p5: "pools ?t = (butlast (pools ?t)) @ [(last (pools ?t))]" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    with p2 p4 have "\<forall>p. p \<in> set (pools ?t) \<longrightarrow> (\<forall>b \<in> set (zerolevelblocklist p). id_ids b (idset ?t) \<and> diff_ids b)"
      by (smt butlast.simps(2) butlast_append in_set_butlastD in_set_conv_decomp_last last.simps last_appendR list.distinct(1))  
  }
  then show ?thesis unfolding inv_ids_def 
    by (simp add: id_ids_valid_def diff_ids_valid_def)
qed

lemma ids_alloc_leaf_case1:
  "lv < curl \<Longrightarrow>
  id_ids (Leaf x) ids \<and> diff_ids (Leaf x) \<Longrightarrow>
  id_ids (fst (alloc (Leaf x) li lv ids curl)) (fst (snd (snd (alloc (Leaf x) li lv ids curl)))) \<and>
  diff_ids (fst (alloc (Leaf x) li lv ids curl))"
  by auto

lemma ids_alloc_leaf_case2:
  "\<not> lv < curl \<Longrightarrow>
  lv = curl \<Longrightarrow>
  id_ids (Leaf x) ids \<and> diff_ids (Leaf x) \<Longrightarrow>
  id_ids (fst (alloc (Leaf x) li lv ids curl)) (fst (snd (snd (alloc (Leaf x) li lv ids curl)))) \<and>
  diff_ids (fst (alloc (Leaf x) li lv ids curl))"
  apply auto
  using snd_conv id_ids_leaf_node(1) i1
  apply metis
  by (simp add: diff1)

lemma ids_alloc_leaf_case3:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) = ALLOC \<Longrightarrow>
  id_ids (Leaf x) ids \<and> diff_ids (Leaf x) \<Longrightarrow>
  id_ids (fst (alloc (Leaf x) li lv ids curl)) (fst (snd (snd (alloc (Leaf x) li lv ids curl)))) \<and>
  diff_ids (fst (alloc (Leaf x) li lv ids curl))"
  by auto

lemma ids_divide:
  "fst (divide (Leaf v) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd (snd ll) \<in> snd (snd (divide (Leaf v) li ids)) \<and>
  snd (snd lr) \<in> snd (snd (divide (Leaf v) li ids)) \<and>
  snd (snd rl) \<in> snd (snd (divide (Leaf v) li ids)) \<and>
  snd (snd rr) \<in> snd (snd (divide (Leaf v) li ids))"
  unfolding divide_def Let_def
    apply auto
  using newid1_in_getnewid
    apply auto
  using newid2_in_getnewid
    apply auto
  using newid3_in_getnewid
   apply auto
  using newid4_in_getnewid
  by auto

lemma ids_alloc_leaf:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newli = fst (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  newids = snd (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd (alloc (Leaf ll) newli lv newids (Suc curl))))"
proof-
  assume a0: "\<not> lv < curl"
     and a1: "lv \<noteq> curl"
     and a2: "fst (snd x) \<noteq> ALLOC"
     and a3: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
     and a4: "newli = fst (snd (divide (Leaf x) li ids))"
     and a5: "newids = snd (snd (divide (Leaf x) li ids))"
  let ?p = "let re = divide (Leaf x) li ids;
                node = fst re;
                freeset = fst (snd re);
                newids = snd (snd re) in
            case node of (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) \<Rightarrow>
              let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
              (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True) |
                         _ \<Rightarrow> (Leaf x, li, ids, False)"
  have p0: "fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd ?p))" using a0 a1 a2 by auto
  let ?b = "let re = divide (Leaf x) li ids;
                node = fst re;
                freeset = fst (snd re);
                newids = snd (snd re) in
            (let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
              (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True))"
  have p1: "?p = ?b" unfolding Let_def using a3 by auto
  let ?newli = "fst (snd (divide (Leaf x) li ids))"
  let ?newids = "snd (snd (divide (Leaf x) li ids))"
  have p2: "fst (snd (snd ?b)) = fst (snd (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl))))"
    unfolding Let_def by auto
  have p3: "fst (snd (snd ?p)) = fst (snd (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl))))"
    using p1 p2 by auto
  have p4: "fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl))))"
    using p0 p3 by auto
  then show ?thesis using a4 a5 by auto
qed

lemma idset_subset2:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  snd (snd x) \<in> ids \<Longrightarrow>
  ids \<subseteq> fst (snd (snd (alloc (Leaf x) li lv ids curl)))"
proof(induct "lv - curl" arbitrary: curl x li ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and pll_alloc: "fst (snd ll) \<noteq> ALLOC"
      and pll_free: "fst (snd ll) = FREE"
    unfolding divide_def Let_def by auto
  have ll_id: "snd (snd ll) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide Suc(6) pdivide by auto
  have ids_belong: "ids \<subseteq> snd (snd (divide (Leaf x) li ids))"
    unfolding divide_def Let_def apply auto
    using getnewid_inc by auto
  let ?li = "fst (snd (divide (Leaf x) li ids))"
  let ?ids = "snd (snd (divide (Leaf x) li ids))"
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto
    have step1: "fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf Suc(3,4,5) pdivide by blast
    have ll_alloc_idset: "fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) = snd (snd (divide (Leaf x) li ids))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free by auto
    have ?case using step1 ll_alloc_idset ids_belong by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(3,4) by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have step2: "fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf Suc(3,4,5) pdivide by auto
    have ids_ll_alloc: "snd (snd (divide (Leaf x) li ids)) \<subseteq> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using Suc(1) xa_lv_suc_curl de_lv_less_suc_curl de_lv_suc_curl pll_alloc ll_id by auto
    have ?case using step2 ids_ll_alloc ids_belong by auto
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma ids_alloc_leaf2:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newli = fst (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  newids = snd (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  snd (snd lr) \<in> fst (snd (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) \<and>
  snd (snd rl) \<in> fst (snd (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) \<and>
  snd (snd rr) \<in> fst (snd (snd (alloc (Leaf ll) newli lv newids (Suc curl))))"
proof-
  assume a0: "\<not> lv < curl"
     and a1: "lv \<noteq> curl"
     and a2: "fst (snd x) \<noteq> ALLOC"
     and a3: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
     and a4: "newli = fst (snd (divide (Leaf x) li ids))"
     and a5: "newids = snd (snd (divide (Leaf x) li ids))"
  have pll_free: "fst (snd ll) = FREE"
    using a3 divide_def Let_def
    by (smt prod.collapse prod.inject tree.inject(1) tree.inject(2) tree.simps(5))
  have pll_alloc: "fst (snd ll) \<noteq> ALLOC"
    using pll_free by auto
  have leaf_belong: "snd (snd lr) \<in> snd (snd (divide (Leaf x) li ids)) \<and>
                     snd (snd rl) \<in> snd (snd (divide (Leaf x) li ids)) \<and>
                     snd (snd rr) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide a3 by auto
  {assume lv_suc_curl: "lv = Suc curl"
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto
    have ll_alloc_idset: "fst (snd (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) = snd (snd (divide (Leaf x) li ids))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free a4 a5 by auto
    have ?thesis using leaf_belong ll_alloc_idset by auto
  }
  moreover
  {assume de_lv_suc_curl: "lv \<noteq> Suc curl"
    have de_lv_less_suc_curl: "\<not> lv < Suc curl"
      by (simp add: a0 a1 not_less_less_Suc_eq)
    have divide_belong: "snd (snd (divide (Leaf x) li ids)) \<subseteq> fst (snd (snd (alloc (Leaf ll) newli lv newids (Suc curl))))"
      using idset_subset2 de_lv_less_suc_curl de_lv_suc_curl pll_alloc leaf_belong a4 a5
      by (simp add: a3 ids_divide)
    have ?thesis using leaf_belong divide_belong by blast
  }
  ultimately have ?thesis by fastforce
  then show ?thesis by auto
qed

lemma ids_finite_ids:
  "finite ids \<Longrightarrow>
  finite (snd (snd (divide (Leaf x) li ids)))"
proof-
  assume a0: "finite ids"
  have p0: "snd (snd (divide (Leaf x) li ids)) = snd (snd (snd (snd (getnewid ids))))"
    unfolding divide_def Let_def by auto
  obtain xa xb xc xd
    where obtain_divide: "snd (snd (divide (Leaf x) li ids)) = ids \<union> {xa, xb, xc, xd}"
    using p0 exists_p_getnewid by (metis sndI)
  have "finite (ids \<union> {xa, xb, xc, xd})" using a0 by auto
  then show ?thesis using obtain_divide by auto
qed

lemma ids_overlap_empty:
  "idsets_block b \<subseteq> ids \<Longrightarrow>
  idsets_block (Leaf x) \<subseteq> ids \<Longrightarrow>
  idsets_block b \<inter> idsets_block (Leaf x) = {} \<Longrightarrow>
  \<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  finite ids \<Longrightarrow>
  idsets_block b \<inter> idsets_block (fst (alloc (Leaf x) li lv ids curl)) = {}"
proof(induct "lv - curl" arbitrary: b curl x li ids)
  case 0
  then show ?case by linarith
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and pll_alloc: "fst (snd ll) \<noteq> ALLOC"
      and pll_free: "fst (snd ll) = FREE"
    unfolding divide_def Let_def by auto
  have diff: "snd (snd ll) \<noteq> snd (snd lr) \<and> snd (snd ll) \<noteq> snd (snd rl) \<and> snd (snd ll) \<noteq> snd (snd rr) \<and>
              snd (snd lr) \<noteq> snd (snd rl) \<and> snd (snd lr) \<noteq> snd (snd rr) \<and>
              snd (snd rl) \<noteq> snd (snd rr)"
    using divide_diff divide_diff2 Suc(9) pdivide by auto
  have diff2: "snd (snd ll) \<notin> ids \<and>
               snd (snd lr) \<notin> ids \<and>
               snd (snd rl) \<notin> ids \<and>
               snd (snd rr) \<notin> ids"
    using divide_diff3 Suc(9) pdivide by auto
  have ll_id: "snd (snd ll) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have lr_id: "snd (snd lr) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have rl_id: "snd (snd rl) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have rr_id: "snd (snd rr) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  let ?li = "fst (snd (divide (Leaf x) li ids))"
  let ?ids = "snd (snd (divide (Leaf x) li ids))"
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_curl: "\<not> lv < curl" using lv_suc_curl by auto
    have de_lv_eq_curl: "\<not> lv = curl" using lv_suc_curl by auto
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    have step1: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h de_lv_less_curl de_lv_eq_curl Suc(8) pdivide by auto
    have ll_alloc: "fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)) = Leaf (fst ll, ALLOC, snd (snd ll))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free by auto
    have co: "idsets_block (Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)) =
              {(snd (snd ll)), (snd (snd lr)), (snd (snd rl)), (snd (snd rr))}"
      using idsets_block.simps ll_alloc diff by auto
    have nobelong: "{(snd (snd ll)), (snd (snd lr)), (snd (snd rl)), (snd (snd rr))} \<inter> idsets_block b = {}"
      using Suc(3) diff2 by auto
    have ?case using step1 co nobelong by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(6,7) by auto
    have de_lv_le_curl: "\<not> lv < curl" using de_lv_less_suc_curl by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_equal_curl: "lv \<noteq> curl" using de_lv_less_suc_curl de_lv_suc_curl by auto

    have step2: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h de_lv_le_curl de_lv_equal_curl Suc(8) pdivide by blast
    have co2: "idsets_block (Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)) =
              idsets_block (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) \<union> {(snd (snd lr)), (snd (snd rl)), (snd (snd rr))}"
      using idsets_block.simps by auto
    have ids_belong: "ids \<subseteq> snd (snd (divide (Leaf x) li ids))"
      unfolding divide_def Let_def apply auto
      using getnewid_inc by auto
    have b_belong: "idsets_block b \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using Suc(3) ids_belong by auto
    have no_overlap: "snd (snd ll) \<notin> idsets_block b"
      using diff2 Suc(3) by auto
    have alloc_ll_overlap: "idsets_block b \<inter> idsets_block (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) = {}"
      using Suc(1) xa_lv_suc_curl b_belong ll_id no_overlap de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(9) ids_finite_ids by auto
    have nobelong2: "(idsets_block (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) \<union> {(snd (snd lr)), (snd (snd rl)), (snd (snd rr))}) \<inter>
                    idsets_block b = {}"
      using alloc_ll_overlap diff2 Suc(3) by auto
    have ?case using step2 co2 nobelong2 by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma ids_overlap_empty2:
  "idsets_block oth \<subseteq> ids \<Longrightarrow>
  idsets_block b \<subseteq> ids \<Longrightarrow>
  idsets_block oth \<inter> idsets_block b = {} \<Longrightarrow>
  \<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  finite ids \<Longrightarrow>
  idsets_block oth \<inter> idsets_block (fst (alloc b li lv ids curl)) = {}"
proof(induct b arbitrary: li lv ids curl oth)
  case (Leaf x)
  then show ?case
    apply(cases "fst (snd x) \<noteq> ALLOC")
    using ids_overlap_empty by auto
next
  case (Node b1 b2 b3 b4)
  have idsets_b1: "idsets_block b1 \<subseteq> ids"
    using Node.prems(2) by auto
  have idsets_b2: "idsets_block b2 \<subseteq> ids"
    using Node.prems(2) by auto
  have idsets_b3: "idsets_block b3 \<subseteq> ids"
    using Node.prems(2) by auto
  have idsets_b4: "idsets_block b4 \<subseteq> ids"
    using Node.prems(2) by auto
  have overlap_b1: "idsets_block oth \<inter> idsets_block b1 = {}"
    using Node.prems(3) by auto
  have overlap_b2: "idsets_block oth \<inter> idsets_block b2 = {}"
    using Node.prems(3) by auto
  have overlap_b3: "idsets_block oth \<inter> idsets_block b3 = {}"
    using Node.prems(3) by auto
  have overlap_b4: "idsets_block oth \<inter> idsets_block b4 = {}"
    using Node.prems(3) by auto
  have de_lv_le_suc_curl: "\<not> lv < Suc curl"
    using Node.prems(4,5) by auto
  {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b1: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    have overlap_alloc_b1: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block oth = {}"
    proof-
      {assume a0: "lv = Suc curl"
        {assume c10: "get_leaf b1 = True"
          obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
          {assume a10: "fst (snd x) = FREE"
            have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
              using alloc.simps(1) a0 a10 by auto
            have ?thesis using c11 a11 overlap_b1 by auto
          }moreover
          {assume a20: "fst (snd x) = ALLOC"
            have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
              using alloc.simps(1) a0 a20 by auto
            have ?thesis using c11 a21 overlap_b1 by auto
          }
          ultimately have ?thesis using block_state_type.exhaust by blast
          then have ?thesis using c11 by simp
        }moreover
        {assume c20: "get_leaf b1 = False"
          obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
          have a30: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
            using alloc.simps(2) a0 by auto
          have ?thesis using c21 a30 overlap_b1 by auto
        }
        ultimately have ?thesis by auto
      }moreover
      {assume b0: "lv \<noteq> Suc curl"
        have ?thesis using Node.hyps(1) Node.prems(1) idsets_b1 overlap_b1 de_lv_le_suc_curl b0 Node.prems(6) by blast
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using alloc_b1 overlap_alloc_b1 overlap_b2 overlap_b3 overlap_b4 by auto
  }
  moreover
  {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b2: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    have overlap_alloc_b2: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block oth = {}"
    proof-
      {assume a0: "lv = Suc curl"
        {assume c10: "get_leaf b2 = True"
          obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
          {assume a10: "fst (snd x) = FREE"
            have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
              using alloc.simps(1) a0 a10 by auto
            have ?thesis using c11 a11 overlap_b2 by auto
          }moreover
          {assume a20: "fst (snd x) = ALLOC"
            have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
              using alloc.simps(1) a0 a20 by auto
            have ?thesis using c11 a21 overlap_b2 by auto
          }
          ultimately have ?thesis using block_state_type.exhaust by blast
          then have ?thesis using c11 by simp
        }moreover
        {assume c20: "get_leaf b2 = False"
          obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
          have a30: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
            using alloc.simps(2) a0 by auto
          have ?thesis using c21 a30 overlap_b2 by auto
        }
        ultimately have ?thesis by auto
      }moreover
      {assume b0: "lv \<noteq> Suc curl"
        have ?thesis using Node.hyps(2) Node.prems(1) idsets_b2 overlap_b2 de_lv_le_suc_curl b0 Node.prems(6) by blast
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using alloc_b2 overlap_alloc_b2 overlap_b1 overlap_b3 overlap_b4 by auto
  }
  moreover
  {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b3: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    have overlap_alloc_b3: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block oth = {}"
    proof-
      {assume a0: "lv = Suc curl"
        {assume c10: "get_leaf b3 = True"
          obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
          {assume a10: "fst (snd x) = FREE"
            have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
              using alloc.simps(1) a0 a10 by auto
            have ?thesis using c11 a11 overlap_b3 by auto
          }moreover
          {assume a20: "fst (snd x) = ALLOC"
            have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
              using alloc.simps(1) a0 a20 by auto
            have ?thesis using c11 a21 overlap_b3 by auto
          }
          ultimately have ?thesis using block_state_type.exhaust by blast
          then have ?thesis using c11 by simp
        }moreover
        {assume c20: "get_leaf b3 = False"
          obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
          have a30: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
            using alloc.simps(2) a0 by auto
          have ?thesis using c21 a30 overlap_b3 by auto
        }
        ultimately have ?thesis by auto
      }moreover
      {assume b0: "lv \<noteq> Suc curl"
        have ?thesis using Node.hyps(3) Node.prems(1) idsets_b3 overlap_b3 de_lv_le_suc_curl b0 Node.prems(6) by blast
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using alloc_b3 overlap_alloc_b3 overlap_b1 overlap_b2 overlap_b4 by auto
  }
  moreover
  {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b4: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    have overlap_alloc_b4: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block oth = {}"
    proof-
      {assume a0: "lv = Suc curl"
        {assume c10: "get_leaf b4 = True"
          obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
          {assume a10: "fst (snd x) = FREE"
            have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
              using alloc.simps(1) a0 a10 by auto
            have ?thesis using c11 a11 overlap_b4 by auto
          }moreover
          {assume a20: "fst (snd x) = ALLOC"
            have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
              using alloc.simps(1) a0 a20 by auto
            have ?thesis using c11 a21 overlap_b4 by auto
          }
          ultimately have ?thesis using block_state_type.exhaust by blast
          then have ?thesis using c11 by simp
        }moreover
        {assume c20: "get_leaf b4 = False"
          obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
          have a30: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
            using alloc.simps(2) a0 by auto
          have ?thesis using c21 a30 overlap_b4 by auto
        }
        ultimately have ?thesis by auto
      }moreover
      {assume b0: "lv \<noteq> Suc curl"
        have ?thesis using Node.hyps(4) Node.prems(1) idsets_b4 overlap_b4 de_lv_le_suc_curl b0 Node.prems(6) by blast
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ?case using alloc_b4 overlap_alloc_b4 overlap_b1 overlap_b2 overlap_b3 by auto
  }
  moreover
  {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
               snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have alloc_b5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    have ?case using alloc_b5 Node.prems(3) by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma ids_alloc_leaf_case4:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_ids (Leaf x) ids \<and> diff_ids (Leaf x) \<Longrightarrow>
  id_ids (fst (alloc (Leaf x) li lv ids curl)) (fst (snd (snd (alloc (Leaf x) li lv ids curl)))) \<and>
  diff_ids (fst (alloc (Leaf x) li lv ids curl))"
proof(induct "lv - curl" arbitrary: curl x li ids)
  case 0
  then show ?case by linarith
next
  case (Suc xa)
  have leaf_hold: "snd (snd x) \<in> ids"
    using Suc(7) id_ids_leaf_node(1) by blast
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and pll_alloc: "fst (snd ll) \<noteq> ALLOC"
      and pll_free: "fst (snd ll) = FREE"
    unfolding divide_def Let_def by auto
  have ll_id: "snd (snd ll) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have lr_id: "snd (snd lr) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have rl_id: "snd (snd rl) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have rr_id: "snd (snd rr) \<in> snd (snd (divide (Leaf x) li ids))"
    using ids_divide pdivide by blast
  have diff_ll: "diff_ids (Leaf ll)"
    using diff1 by auto
  have diff_lr: "diff_ids (Leaf lr)"
    using diff1 by auto
  have diff_rl: "diff_ids (Leaf rl)"
    using diff1 by auto
  have diff_rr: "diff_ids (Leaf rr)"
    using diff1 by auto
  have diff: "snd (snd ll) \<noteq> snd (snd lr) \<and> snd (snd ll) \<noteq> snd (snd rl) \<and> snd (snd ll) \<noteq> snd (snd rr) \<and>
              snd (snd lr) \<noteq> snd (snd rl) \<and> snd (snd lr) \<noteq> snd (snd rr) \<and>
              snd (snd rl) \<noteq> snd (snd rr)"
    using divide_diff divide_diff2 Suc(6) pdivide by auto
  have diff_bc: "idsets_block (Leaf lr) \<inter> idsets_block (Leaf rl) = {}"
    by (simp add: diff) 
  have diff_bd: "idsets_block (Leaf lr) \<inter> idsets_block (Leaf rr) = {}"
    by (simp add: diff) 
  have diff_cd: "idsets_block (Leaf rl) \<inter> idsets_block (Leaf rr) = {}"
    by (simp add: diff) 
  let ?li = "fst (snd (divide (Leaf x) li ids))"
  let ?ids = "snd (snd (divide (Leaf x) li ids))"
  have id_ids_ll: "id_ids (Leaf ll) ?ids"
    using ll_id by (simp add: i1)
  have id_ids_lr: "id_ids (Leaf lr) ?ids"
    using lr_id by (simp add: i1)
  have id_ids_rl: "id_ids (Leaf rl) ?ids"
    using rl_id by (simp add: i1)
  have id_ids_rr: "id_ids (Leaf rr) ?ids"
    using rr_id by (simp add: i1)

  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_curl: "\<not> lv < curl" using lv_suc_curl by auto
    have de_lv_eq_curl: "\<not> lv = curl" using lv_suc_curl by auto
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    have step1: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h de_lv_less_curl de_lv_eq_curl Suc(5) pdivide by auto
    have ll_alloc: "fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)) = Leaf (fst ll, ALLOC, snd (snd ll))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free by auto
    have idset_change: "fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf de_lv_less_curl de_lv_eq_curl Suc(5) pdivide by auto

    have id_ids_ll_alloc: "id_ids (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using ids_alloc_leaf_case2 de_lv_less_suc_curl lv_suc_curl id_ids_ll diff_ll by (simp add: i1)
    have lr_ids_belong: "snd (snd lr) \<in> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf2 Suc(3,4,5) leaf_hold pdivide by auto
    have id_ids_lr_change: "id_ids (Leaf lr) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using lr_ids_belong by (simp add: i1)
    have rl_ids_belong: "snd (snd rl) \<in> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf2 Suc(3,4,5) leaf_hold pdivide by auto
    have id_ids_rl_change: "id_ids (Leaf rl) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using rl_ids_belong by (simp add: i1)
    have rr_ids_belong: "snd (snd rr) \<in> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf2 Suc(3,4,5) leaf_hold pdivide by auto
    have id_ids_rr_change: "id_ids (Leaf rr) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using rr_ids_belong by (simp add: i1)
    have id_ids_x_alloc: "id_ids (fst (alloc (Leaf x) li lv ids curl)) (fst (snd (snd (alloc (Leaf x) li lv ids curl))))"
      using step1 id_ids_ll_alloc id_ids_lr_change id_ids_rl_change id_ids_rr_change idset_change by (simp add: i2)

    have diff_ids_ll_alloc: "diff_ids (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)))"
      using diff1 ll_alloc by auto
    have diff_ids_x_alloc: "diff_ids (fst (alloc (Leaf x) li lv ids curl))"
      using step1 ll_alloc diff diff_ids_ll_alloc diff_lr diff_rl diff_rr by (simp add: diff2)

    then have ?case using id_ids_x_alloc by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(3,4) by auto
    have de_lv_le_curl: "\<not> lv < curl" using de_lv_less_suc_curl by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_equal_curl: "lv \<noteq> curl" using de_lv_less_suc_curl de_lv_suc_curl by auto

    have step2: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h Suc(3,4,5) pdivide by auto
    have idset_change2: "fst (snd (snd (alloc (Leaf x) li lv ids curl))) = fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf de_lv_le_curl de_lv_equal_curl Suc(5) pdivide by auto

    have id_ids_ll_alloc2: "id_ids (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using Suc(1) xa_lv_suc_curl de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(6) id_ids_ll diff_ll by (simp add:ids_finite_ids)
    have lr_ids_belong2: "snd (snd lr) \<in> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf2 Suc(3,4,5) leaf_hold pdivide by auto
    have id_ids_lr_change2: "id_ids (Leaf lr) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using lr_ids_belong2 by (simp add: i1)
    have rl_ids_belong2: "snd (snd rl) \<in> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf2 Suc(3,4,5) leaf_hold pdivide by auto
    have id_ids_rl_change2: "id_ids (Leaf rl) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using rl_ids_belong2 by (simp add: i1)
    have rr_ids_belong2: "snd (snd rr) \<in> fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using ids_alloc_leaf2 Suc(3,4,5) leaf_hold pdivide by auto
    have id_ids_rr_change2: "id_ids (Leaf rr) (fst (snd (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))))"
      using rr_ids_belong2 by (simp add: i1)
    have id_ids_x_alloc2: "id_ids (fst (alloc (Leaf x) li lv ids curl)) (fst (snd (snd (alloc (Leaf x) li lv ids curl))))"
      using step2 id_ids_ll_alloc2 id_ids_lr_change2 id_ids_rl_change2 id_ids_rr_change2 idset_change2 by (simp add:i2)

    have diff_ids_ll_alloc2: "diff_ids (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(6) id_ids_ll diff_ll by (simp add:ids_finite_ids)

    have p0: "idsets_block (Leaf lr) \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using idsets_block.simps(1) lr_id by auto
    have p1: "idsets_block (Leaf ll) \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using idsets_block.simps(1) ll_id by auto
    have p2: "idsets_block (Leaf lr) \<inter> idsets_block (Leaf ll) = {}"
      by (simp add: diff)
    have diff_alloc_ll_lr: "idsets_block (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) \<inter> idsets_block (Leaf lr) = {}"
      using ids_overlap_empty p0 p1 p2 de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(6) ids_finite_ids
      by (metis inf_commute) 

    have p00: "idsets_block (Leaf rl) \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using idsets_block.simps(1) rl_id by auto
    have p11: "idsets_block (Leaf ll) \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using idsets_block.simps(1) ll_id by auto
    have p22: "idsets_block (Leaf rl) \<inter> idsets_block (Leaf ll) = {}"
      by (simp add: diff)
    have diff_alloc_ll_rl: "idsets_block (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) \<inter> idsets_block (Leaf rl) = {}"
      using ids_overlap_empty p00 p11 p22 de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(6) ids_finite_ids
      by (metis inf_commute) 

    have p000: "idsets_block (Leaf rr) \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using idsets_block.simps(1) rr_id by auto
    have p111: "idsets_block (Leaf ll) \<subseteq> snd (snd (divide (Leaf x) li ids))"
      using idsets_block.simps(1) ll_id by auto
    have p222: "idsets_block (Leaf rr) \<inter> idsets_block (Leaf ll) = {}"
      by (simp add: diff)
    have diff_alloc_ll_rr: "idsets_block (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) \<inter> idsets_block (Leaf rr) = {}"
      using ids_overlap_empty p000 p111 p222 de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(6) ids_finite_ids
      by (metis inf_commute) 

    have diff_ids_x_alloc2: "diff_ids (fst (alloc (Leaf x) li lv ids curl))"
      using step2 diff_alloc_ll_lr diff_alloc_ll_rl diff_alloc_ll_rr diff_bc diff_bd diff_cd 
      diff_ids_ll_alloc2 diff_lr diff_rl diff_rr by (simp add: diff2)

    then have ?case using id_ids_x_alloc2 by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma ids_alloc_node_h:
  "id_ids b ids \<and> diff_ids b \<Longrightarrow>
  finite ids \<Longrightarrow>
  lv = curl \<Longrightarrow>
  id_ids (fst (alloc b li lv ids curl)) (fst (snd (snd (alloc b li lv ids curl)))) \<and>
  diff_ids (fst (alloc b li lv ids curl))"
proof(induct b)
  case (Leaf x)
  then show ?case using ids_alloc_leaf_case2 by auto
next
  case (Node b1 b2 b3 b4)
  have ids_node: "id_ids (Node b1 b2 b3 b4) ids \<and> diff_ids (Node b1 b2 b3 b4)"
    by (simp add: Node.prems(1))
  assume a0: "lv = curl"
  have lv_le_suc_curl: "lv < Suc curl" using a0 by auto
  have "id_ids (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) (fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)))) \<and>
        diff_ids (fst (alloc (Node b1 b2 b3 b4) li lv ids curl))"
    using alloc.simps(2) lv_le_suc_curl ids_node by auto
  then show ?case by auto
qed

lemma idset_subset3_h:
  "lv > curl \<Longrightarrow>
  id_ids (Node b1 b2 b3 b4) ids \<Longrightarrow>
  ids \<subseteq> fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)))"
proof(induct "lv - curl" arbitrary: curl b1 b2 b3 b4 li ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have id_ids_b1: "id_ids b1 ids"
    using Suc(4) id_ids_leaf_node(2) by blast
  have id_ids_b2: "id_ids b2 ids"
    using Suc(4) id_ids_leaf_node(2) by blast
  have id_ids_b3: "id_ids b3 ids"
    using Suc(4) id_ids_leaf_node(2) by blast
  have id_ids_b4: "id_ids b4 ids"
    using Suc(4) id_ids_leaf_node(2) by blast
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have idset_b1: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    have "ids \<subseteq> fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have ?thesis using c11 a11 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 a30 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b1 by auto
    }
    moreover
    {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have idset_b2: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    have "ids \<subseteq> fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have ?thesis using c11 a11 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 a30 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b2 by auto
    }
    moreover
    {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have idset_b3: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    have "ids \<subseteq> fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have ?thesis using c11 a11 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 a30 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b3 by auto
    }
    moreover
    {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have idset_b4: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    have "ids \<subseteq> fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have ?thesis using c11 a11 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 a30 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b4 by auto
    }
    moreover
    {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have idset_b5: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = ids"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    then have ?case by auto
    }
    ultimately have ?case by blast
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_le_suc_suc_curl: "\<not> lv < Suc (Suc curl)" using xa_gr_1 xa_lv_suc_curl by auto
    have lv_gr_suc_curl: "lv > Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_gr_suc_curl by auto
    have de_lv_eq_suc_curl: "lv \<noteq> Suc curl" using lv_gr_suc_curl by auto

    {assume c11: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have idset_b11: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c11 by auto
    have idsub_b11: "ids \<subseteq> fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "snd (snd x) \<in> ids"
          using id_ids_b1 c11 id_ids_leaf_node(1) by blast
        then have ?thesis using c11 lv_gr_suc_curl idset_subset2 by auto
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have ?thesis using Suc(1) xa_lv_suc_curl lv_gr_suc_curl id_ids_b1 c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b11 by auto
    }
    moreover
    {assume c22: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have idset_b22: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c22 by auto
    have idsub_b22: "ids \<subseteq> fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "snd (snd x) \<in> ids"
          using id_ids_b2 c11 id_ids_leaf_node(1) by blast
        then have ?thesis using c11 lv_gr_suc_curl idset_subset2 by auto
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have ?thesis using Suc(1) xa_lv_suc_curl lv_gr_suc_curl id_ids_b2 c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b22 by auto
    }
    moreover
    {assume c33: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have idset_b33: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c33 by auto
    have idsub_b33: "ids \<subseteq> fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "snd (snd x) \<in> ids"
          using id_ids_b3 c11 id_ids_leaf_node(1) by blast
        then have ?thesis using c11 lv_gr_suc_curl idset_subset2 by auto
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have ?thesis using Suc(1) xa_lv_suc_curl lv_gr_suc_curl id_ids_b3 c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b33 by auto
    }
    moreover
    {assume c44: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have idset_b44: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c44 by auto
    have idsub_b44: "ids \<subseteq> fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        have "snd (snd x) \<in> ids"
          using id_ids_b4 c11 id_ids_leaf_node(1) by blast
        then have ?thesis using c11 lv_gr_suc_curl idset_subset2 by auto
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have ?thesis using Suc(1) xa_lv_suc_curl lv_gr_suc_curl id_ids_b4 c21 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    then have ?case using idset_b44 by auto
    }
    moreover
    {assume c55: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have idset_b55: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = ids"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    then have ?case by auto
    }
    ultimately have ?case by blast
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma idset_subset3:
  "lv > curl \<Longrightarrow>
  id_ids b ids \<Longrightarrow>
  ids \<subseteq> fst (snd (snd (alloc b li lv ids curl)))"
proof(induct b)
  case (Leaf x)
  have "snd (snd x) \<in> ids"
    using Leaf.prems(2) id_ids_leaf_node(1) by blast
  then show ?case
    using Leaf.prems(1) idset_subset2 by auto
next
  case (Node b1 b2 b3 b4)
  then show ?case using idset_subset3_h by auto
qed

lemma ids_alloc_node:
  "id_ids (Node b1 b2 b3 b4) ids \<and> diff_ids (Node b1 b2 b3 b4) \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < Suc curl \<Longrightarrow>
  id_ids (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) (fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)))) \<and>
  diff_ids (fst (alloc (Node b1 b2 b3 b4) li lv ids curl))"
proof(induct "lv - curl" arbitrary: curl b1 b2 b3 b4 li ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have ids_b1: "id_ids b1 ids"
    using Suc(3) id_ids_leaf_node(2) by blast
  have ids_b2: "id_ids b2 ids"
    using Suc(3) id_ids_leaf_node(2) by blast
  have ids_b3: "id_ids b3 ids"
    using Suc(3) id_ids_leaf_node(2) by blast
  have ids_b4: "id_ids b4 ids"
    using Suc(3) id_ids_leaf_node(2) by blast
  have diff_b1: "diff_ids b1"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_b2: "diff_ids b2"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_b3: "diff_ids b3"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_b4: "diff_ids b4"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_ab: "idsets_block b1 \<inter> idsets_block b2 = {}"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_ac: "idsets_block b1 \<inter> idsets_block b3 = {}"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_ad: "idsets_block b1 \<inter> idsets_block b4 = {}"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_bc: "idsets_block b2 \<inter> idsets_block b3 = {}"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_bd: "idsets_block b2 \<inter> idsets_block b4 = {}"
    using Suc(3) diff_ids_leaf_node(2) by blast
  have diff_cd: "idsets_block b3 \<inter> idsets_block b4 = {}"
    using Suc(3) diff_ids_leaf_node(2) by blast
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b1: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    have idset_b1: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto

    have ids_alloc_b1: "id_ids (fst (alloc b1 li lv ids (Suc curl))) (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using ids_alloc_node_h ids_b1 diff_b1 Suc(4) lv_suc_curl by auto
    have ids_alloc_b1_b2: "id_ids b2 (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc b1 li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 ids_b2 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc b1 li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 ids_b2 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 ids_b2 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b1_b3: "id_ids b3 (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc b1 li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 ids_b3 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc b1 li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 ids_b3 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 ids_b3 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b1_b4: "id_ids b4 (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc b1 li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 ids_b4 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc b1 li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 ids_b4 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 ids_b4 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_node_b1: "id_ids (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using ids_alloc_b1 ids_alloc_b1_b2 ids_alloc_b1_b3 ids_alloc_b1_b4 by (simp add: i2)

    have diff_ids_alloc_b1: "diff_ids (fst (alloc b1 li lv ids (Suc curl)))"
      using ids_alloc_node_h ids_b1 diff_b1 Suc(4) lv_suc_curl by auto
    have diff_alloc_b1_b2: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block b2 = {}"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_ab by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_ab by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_ab by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b1_b3: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block b3 = {}"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_ac by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_ac by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_ac by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b1_b4: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block b4 = {}"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_ad by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_ad by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_ad by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_node_b1: "diff_ids (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4)"
      using diff_ids_alloc_b1 diff_b2 diff_b3 diff_b4 
      using diff_alloc_b1_b2 diff_alloc_b1_b3 diff_alloc_b1_b4 diff_bc diff_bd diff_cd 
      by (simp add: diff2)
    have ?case using alloc_b1 idset_b1 ids_node_b1 diff_node_b1 by auto
    }
    moreover
    {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b2: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    have idset_b2: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto

    have ids_alloc_b2: "id_ids (fst (alloc b2 li lv ids (Suc curl))) (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using ids_alloc_node_h ids_b2 diff_b2 Suc(4) lv_suc_curl by auto
    have ids_alloc_b2_b1: "id_ids b1 (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b1 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b1 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b1 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b1 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b1 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b1 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b2_b3: "id_ids b3 (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b3 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b3 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b3 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b3 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b3 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b3 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b2_b4: "id_ids b4 (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b4 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b4 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b4 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b4 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b4 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b4 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_node_b2: "id_ids (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using ids_alloc_b2 ids_alloc_b2_b1 ids_alloc_b2_b3 ids_alloc_b2_b4 by (simp add: i2)

    have diff_ids_alloc_b2: "diff_ids (fst (alloc b2 li lv ids (Suc curl)))"
      using ids_alloc_node_h ids_b2 diff_b2 Suc(4) lv_suc_curl by auto
    have diff_alloc_b2_b1: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block b1 = {}"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_ab by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_ab by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_ab by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b2_b3: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block b3 = {}"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_bc by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_bc by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_bc by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b2_b4: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block b4 = {}"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_bd by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_bd by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_bd by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_node_b2: "diff_ids (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4)"
      using diff_b1 diff_ids_alloc_b2 diff_b3 diff_b4
      using diff_alloc_b2_b1 diff_ac diff_ad diff_alloc_b2_b3 diff_alloc_b2_b4 diff_cd
      by (simp add: diff2 inf_commute)
    have ?case using alloc_b2 idset_b2 ids_node_b2 diff_node_b2 by auto
    }
    moreover
    {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b3: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    have idset_b3: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto

    have ids_alloc_b3: "id_ids (fst (alloc b3 li lv ids (Suc curl))) (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using ids_alloc_node_h ids_b3 diff_b3 Suc(4) lv_suc_curl by auto
    have ids_alloc_b3_b1: "id_ids b1 (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b1 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b1 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b1 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b1 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b1 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b1 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b3_b2: "id_ids b2 (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b2 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b2 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b2 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b2 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b2 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b2 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b3_b4: "id_ids b4 (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b4 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b4 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b4 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b4 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b4 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b4 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_node_b3: "id_ids (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using ids_alloc_b3 ids_alloc_b3_b1 ids_alloc_b3_b2 ids_alloc_b3_b4 by (simp add: i2)

    have diff_ids_alloc_b3: "diff_ids (fst (alloc b3 li lv ids (Suc curl)))"
      using ids_alloc_node_h ids_b3 diff_b3 Suc(4) lv_suc_curl by auto
    have diff_alloc_b3_b1: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block b1 = {}"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_ac by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_ac by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_ac by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b3_b2: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block b2 = {}"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_bc by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_bc by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_bc by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b3_b4: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block b4 = {}"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_cd by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_cd by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_cd by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_node_b3: "diff_ids (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4)"
      using diff_b1 diff_b2 diff_ids_alloc_b3 diff_b4
      using diff_ab diff_alloc_b3_b1 diff_ad diff_alloc_b3_b2 diff_bd diff_alloc_b3_b4
      by (simp add: diff2 inf_commute)
    have ?case using alloc_b3 idset_b3 ids_node_b3 diff_node_b3 by auto
    }
    moreover
    {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b4: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    have idset_b4: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto

    have ids_alloc_b4: "id_ids (fst (alloc b4 li lv ids (Suc curl))) (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using ids_alloc_node_h ids_b4 diff_b4 Suc(4) lv_suc_curl by auto
    have ids_alloc_b4_b1: "id_ids b1 (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b1 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b1 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b1 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b1 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b1 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b1 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b4_b2: "id_ids b2 (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b2 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b2 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b2 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b2 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b2 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b2 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_alloc_b4_b3: "id_ids b3 (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "id_ids b3 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))" 
            using ids_b3 a11 by auto
          have ?thesis using c11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))) = ids"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have a22: "id_ids b3 (fst (snd (snd (alloc (Leaf x) li lv ids (Suc curl)))))"
            using ids_b3 a21 by auto
          have ?thesis using c11 a22 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))) = ids"
          using alloc.simps(2) lv_suc_curl by auto
        have a31: "id_ids b3 (fst (snd (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)))))"
          using ids_b3 a30 by auto
        have ?thesis using c21 a31 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have ids_node_b4: "id_ids (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using ids_alloc_b4 ids_alloc_b4_b1 ids_alloc_b4_b2 ids_alloc_b4_b3 by (simp add: i2)

    have diff_ids_alloc_b4: "diff_ids (fst (alloc b4 li lv ids (Suc curl)))"
      using ids_alloc_node_h ids_b4 diff_b4 Suc(4) lv_suc_curl by auto
    have diff_alloc_b4_b1: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block b1 = {}"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_ad by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_ad by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_ad by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b4_b2: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block b2 = {}"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_bd by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_bd by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_bd by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_alloc_b4_b3: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block b3 = {}"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf (fst x, ALLOC, snd (snd x)))"
            using alloc.simps(1) c11 lv_suc_curl a10 by auto
          have ?thesis using c11 a11 diff_cd by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (alloc (Leaf x) li lv ids (Suc curl)) = (Leaf x)"
            using alloc.simps(1) c11 lv_suc_curl a20 by auto
          have ?thesis using c11 a21 diff_cd by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl)) = (Node m1 m2 m3 m4)"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 c22 diff_cd by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have diff_node_b4: "diff_ids (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl))))"
      using diff_b1 diff_b2 diff_b3 diff_ids_alloc_b4
      using diff_ab diff_ac diff_alloc_b4_b1 diff_bc diff_alloc_b4_b2 diff_alloc_b4_b3
      by (simp add: diff2 inf_commute)
    have ?case using alloc_b4 idset_b4 ids_node_b4 diff_node_b4 by auto
    }
    moreover
    {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have alloc_b5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    have idset_b5: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = ids"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    have ?case using Suc(3) alloc_b5 idset_b5 by auto
    }
    ultimately have ?case by blast
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_le_suc_suc_curl: "\<not> lv < Suc (Suc curl)" using xa_gr_1 xa_lv_suc_curl by auto
    have lv_gr_suc_curl: "lv > Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_gr_suc_curl by auto
    have de_lv_eq_suc_curl: "lv \<noteq> Suc curl" using lv_gr_suc_curl by auto

    have ids_b1_subset: "idsets_block b1 \<subseteq> ids"
      using ids_b1 idsets_block_id_ids by auto
    have ids_b2_subset: "idsets_block b2 \<subseteq> ids"
      using ids_b2 idsets_block_id_ids by auto
    have ids_b3_subset: "idsets_block b3 \<subseteq> ids"
      using ids_b3 idsets_block_id_ids by auto
    have ids_b4_subset: "idsets_block b4 \<subseteq> ids"
      using ids_b4 idsets_block_id_ids by auto

    {assume c11: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b11: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c11 by auto
    have idset_b11: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c11 by auto
    have idsub_b11: "ids \<subseteq> fst (snd (snd (alloc b1 li lv ids (Suc curl))))"
      using idset_subset3 lv_gr_suc_curl ids_b1 by auto

    have ids_alloc_b11: "id_ids (fst (alloc b1 li lv ids (Suc curl))) (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using Suc(1) xa_lv_suc_curl ids_b1 diff_b1 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have ids_alloc_b11_b2: "id_ids b2 (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b2 idsub_b11 by auto
    have ids_alloc_b11_b3: "id_ids b3 (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b3 idsub_b11 by auto
    have ids_alloc_b11_b4: "id_ids b4 (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b4 idsub_b11 by auto
    have ids_node_b11: "id_ids (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) (fst (snd (snd (alloc b1 li lv ids (Suc curl)))))"
      using ids_alloc_b11 ids_alloc_b11_b2 ids_alloc_b11_b3 ids_alloc_b11_b4 by (simp add: i2)

    have diff_ids_alloc_b11: "diff_ids (fst (alloc b1 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl ids_b1 diff_b1 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have diff_alloc_b11_b2: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block b2 = {}"
      using ids_overlap_empty2 ids_b1_subset ids_b2_subset diff_ab de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b11_b3: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block b3 = {}"
      using ids_overlap_empty2 ids_b1_subset ids_b3_subset diff_ac de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b11_b4: "idsets_block (fst (alloc b1 li lv ids (Suc curl))) \<inter> idsets_block b4 = {}"
      using ids_overlap_empty2 ids_b1_subset ids_b4_subset diff_ad de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_node_b11: "diff_ids (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4)"
      using diff_ids_alloc_b11 diff_b2 diff_b3 diff_b4
      using diff_alloc_b11_b2 diff_alloc_b11_b3 diff_alloc_b11_b4 diff_bc diff_bd diff_cd
      by (simp add: diff2)
    have ?case using alloc_b11 idset_b11 ids_node_b11 diff_node_b11 by auto
    }
    moreover
    {assume c22: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b22: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c22 by auto
    have idset_b22: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c22 by auto
    have idsub_b22: "ids \<subseteq> fst (snd (snd (alloc b2 li lv ids (Suc curl))))"
      using idset_subset3 lv_gr_suc_curl ids_b2 by auto

    have ids_alloc_b22: "id_ids (fst (alloc b2 li lv ids (Suc curl))) (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using Suc(1) xa_lv_suc_curl ids_b2 diff_b2 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have ids_alloc_b22_b1: "id_ids b1 (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b1 idsub_b22 by auto
    have ids_alloc_b22_b3: "id_ids b3 (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b3 idsub_b22 by auto
    have ids_alloc_b22_b4: "id_ids b4 (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b4 idsub_b22 by auto
    have ids_node_b22: "id_ids (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) (fst (snd (snd (alloc b2 li lv ids (Suc curl)))))"
      using ids_alloc_b22 ids_alloc_b22_b1 ids_alloc_b22_b3 ids_alloc_b22_b4 by (simp add: i2)

    have diff_ids_alloc_b22: "diff_ids (fst (alloc b2 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl ids_b2 diff_b2 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have diff_alloc_b22_b1: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block b1 = {}"
      using ids_overlap_empty2 ids_b2_subset ids_b1_subset diff_ab de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b22_b3: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block b3 = {}"
      using ids_overlap_empty2 ids_b2_subset ids_b3_subset diff_bc de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b22_b4: "idsets_block (fst (alloc b2 li lv ids (Suc curl))) \<inter> idsets_block b4 = {}"
      using ids_overlap_empty2 ids_b2_subset ids_b4_subset diff_bd de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_node_b22: "diff_ids (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4)"
      using diff_ids_alloc_b22 diff_b1 diff_b3 diff_b4
      using diff_alloc_b22_b1 diff_alloc_b22_b3 diff_alloc_b22_b4 diff_ac diff_ad diff_cd
      by (simp add: diff2 inf_commute)
    have ?case using alloc_b22 idset_b22 ids_node_b22 diff_node_b22 by auto
    }
    moreover
    {assume c33: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b33: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c33 by auto
    have idset_b33: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c33 by auto
    have idsub_b33: "ids \<subseteq> fst (snd (snd (alloc b3 li lv ids (Suc curl))))"
      using idset_subset3 lv_gr_suc_curl ids_b3 by auto

    have ids_alloc_b33: "id_ids (fst (alloc b3 li lv ids (Suc curl))) (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using Suc(1) xa_lv_suc_curl ids_b3 diff_b3 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have ids_alloc_b33_b1: "id_ids b1 (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b1 idsub_b33 by auto
    have ids_alloc_b33_b2: "id_ids b2 (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b2 idsub_b33 by auto
    have ids_alloc_b33_b4: "id_ids b4 (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b4 idsub_b33 by auto
    have ids_node_b33: "id_ids (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) (fst (snd (snd (alloc b3 li lv ids (Suc curl)))))"
      using ids_alloc_b33 ids_alloc_b33_b1 ids_alloc_b33_b2 ids_alloc_b33_b4 by (simp add: i2)

    have diff_ids_alloc_b33: "diff_ids (fst (alloc b3 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl ids_b3 diff_b3 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have diff_alloc_b33_b1: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block b1 = {}"
      using ids_overlap_empty2 ids_b3_subset ids_b1_subset diff_ac de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b33_b2: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block b2 = {}"
      using ids_overlap_empty2 ids_b3_subset ids_b2_subset diff_bc de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b33_b4: "idsets_block (fst (alloc b3 li lv ids (Suc curl))) \<inter> idsets_block b4 = {}"
      using ids_overlap_empty2 ids_b3_subset ids_b4_subset diff_cd de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_node_b33: "diff_ids (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4)"
      using diff_ids_alloc_b33 diff_b1 diff_b2 diff_b4
      using diff_alloc_b33_b1 diff_alloc_b33_b2 diff_alloc_b33_b4 diff_ab diff_ad diff_bd
      by (simp add: diff2 inf_commute)
    have ?case using alloc_b33 idset_b33 ids_node_b33 diff_node_b33 by auto
    }
    moreover
    {assume c44: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b44: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c44 by auto
    have idset_b44: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c44 by auto
    have idsub_b44: "ids \<subseteq> fst (snd (snd (alloc b4 li lv ids (Suc curl))))"
      using idset_subset3 lv_gr_suc_curl ids_b4 by auto

    have ids_alloc_b44: "id_ids (fst (alloc b4 li lv ids (Suc curl))) (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using Suc(1) xa_lv_suc_curl ids_b4 diff_b4 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have ids_alloc_b44_b1: "id_ids b1 (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b1 idsub_b44 by auto
    have ids_alloc_b44_b2: "id_ids b2 (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b2 idsub_b44 by auto
    have ids_alloc_b44_b3: "id_ids b3 (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using id_ids_ext ids_b3 idsub_b44 by auto
    have ids_node_b44: "id_ids (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) (fst (snd (snd (alloc b4 li lv ids (Suc curl)))))"
      using ids_alloc_b44 ids_alloc_b44_b1 ids_alloc_b44_b2 ids_alloc_b44_b3 by (simp add: i2)

    have diff_ids_alloc_b44: "diff_ids (fst (alloc b4 li lv ids (Suc curl)))"
      using Suc(1) xa_lv_suc_curl ids_b4 diff_b4 Suc(4) de_lv_le_suc_suc_curl
      by (metis (full_types) de_lv_eq_suc_curl ids_alloc_leaf_case1 ids_alloc_leaf_case3 ids_alloc_leaf_case4 tree.exhaust)
    have diff_alloc_b44_b1: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block b1 = {}"
      using ids_overlap_empty2 ids_b4_subset ids_b1_subset diff_ad de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b44_b2: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block b2 = {}"
      using ids_overlap_empty2 ids_b4_subset ids_b2_subset diff_bd de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_alloc_b44_b3: "idsets_block (fst (alloc b4 li lv ids (Suc curl))) \<inter> idsets_block b3 = {}"
      using ids_overlap_empty2 ids_b4_subset ids_b3_subset diff_cd de_lv_le_suc_curl de_lv_eq_suc_curl Suc(4) by blast
    have diff_node_b44: "diff_ids (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl))))"
      using diff_ids_alloc_b44 diff_b1 diff_b2 diff_b3
      using diff_alloc_b44_b1 diff_alloc_b44_b2 diff_alloc_b44_b3 diff_ab diff_ac diff_bc
      by (simp add: diff2 inf_commute)
    have ?case using alloc_b44 idset_b44 ids_node_b44 diff_node_b44 by auto
    }
    moreover
    {assume c55: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have alloc_b55: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    have idset_b55: "fst (snd (snd (alloc (Node b1 b2 b3 b4) li lv ids curl))) = ids"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    have ?case using Suc(3) alloc_b55 idset_b55 by auto
    }
    ultimately have ?case by blast
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma inv_ids_alloc:
  "id_ids b ids \<and> diff_ids b \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (alloc b li lv ids curl))) = True \<Longrightarrow>
  id_ids (fst (alloc b li lv ids curl)) (fst (snd (snd (alloc b li lv ids curl)))) \<and>
  diff_ids (fst (alloc b li lv ids curl))"
proof(induct b)
  case (Leaf x)
  then show ?case using ids_alloc_leaf_case1 ids_alloc_leaf_case2 ids_alloc_leaf_case3 ids_alloc_leaf_case4
    by metis
next
  case (Node b1 b2 b3 b4)
  then show ?case using ids_alloc_node by auto
qed

lemma pool_alloc_ids_case1:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  id_ids_valid (fst (pool_alloc po lv n ids)) (fst (snd (pool_alloc po lv n ids))) \<and>
  diff_ids_valid (fst (pool_alloc po lv n ids))"
proof-
  assume a0: "id_ids_valid po ids \<and> diff_ids_valid po"
     and a1: "\<not> lv < 0"
     and a2: "finite ids"
     and a3: "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). id_ids b ids \<and> diff_ids b" using a0 id_ids_valid_def diff_ids_valid_def by blast 
  have p1: "id_ids (zerolevelblocklist po ! n) ids \<and> diff_ids (zerolevelblocklist po ! n)" using p0 a3 by auto
  have p2: "id_ids (fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)) (fst (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))) \<and>
           diff_ids (fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))"
    using inv_ids_alloc p1 a2 a3 by auto
  let ?re = "let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! n) (freelist po) lv ids 0
              in (po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)"
  {
    have p3: "fst (pool_alloc po lv n ids) = fst ?re" apply simp using a3 Let_def by (smt fst_conv)
    have p4: "fst (snd (pool_alloc po lv n ids)) = fst (snd ?re)" apply simp using a3 Let_def by (smt fst_conv snd_conv)
    moreover
    have p5: "(zerolevelblocklist (fst ?re) ! n) = fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)" unfolding Let_def using a3 by auto
    have p6: "(fst (snd ?re)) = fst (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))" unfolding Let_def using a3 by auto
    have p7: "id_ids (zerolevelblocklist (fst ?re) ! n) (fst (snd ?re)) \<and>
             diff_ids (zerolevelblocklist (fst ?re) ! n)"
      using p2 p5 p6 by auto
    have ids_sub: "ids \<subseteq> fst (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))"
    proof-
      {assume c0: "lv = 0"
        {assume c10: "get_leaf (zerolevelblocklist po ! n) = True"
          obtain x where c11: "(zerolevelblocklist po ! n) = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
          {assume a10: "fst (snd x) = FREE"
            have a11: "fst (snd (snd (alloc (Leaf x) (freelist po) lv ids 0))) = ids"
              using alloc.simps(1) c0 a10 by auto
            have ?thesis using c11 a11 by auto
          }moreover
          {assume a20: "fst (snd x) = ALLOC"
            have a21: "fst (snd (snd (alloc (Leaf x) (freelist po) lv ids 0))) = ids"
              using alloc.simps(1) c0 a20 by auto
            have ?thesis using c11 a21 by auto
          }
          ultimately have ?thesis using block_state_type.exhaust by blast
          then have ?thesis using c11 by simp
        }
        moreover
        {assume c20: "get_leaf (zerolevelblocklist po ! n) = False"
          obtain m1 m2 m3 m4 where c21: "(zerolevelblocklist po ! n) = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
          have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) (freelist po) lv ids 0))) = ids"
            using alloc.simps(2) c0 by auto
          have ?thesis using c21 a30 by auto
        }
        ultimately have ?thesis by auto
        then have ?thesis by auto
      }
      moreover
      {assume c1: "lv > 0"
        have ?thesis using idset_subset3 c1 p1 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    with p0 have p00: "\<forall>b \<in> set (zerolevelblocklist po). id_ids b (fst (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))) \<and>
                                                         diff_ids b"
      using id_ids_ext by auto
    with p7 have p8: "\<forall>b \<in> set (zerolevelblocklist (fst ?re)). id_ids b (fst (snd ?re)) \<and>
                                                               diff_ids b"
      unfolding Let_def apply auto
      using p2 set_update_subset_insert apply fastforce
      by (metis in_set_conv_nth length_list_update nth_list_update_neq)
    have p9: "id_ids_valid (fst ?re) (fst (snd ?re)) \<and> diff_ids_valid (fst ?re)"
      unfolding id_ids_valid_def diff_ids_valid_def using p8 by auto
    with p3 p4 have p10: "id_ids_valid (fst (pool_alloc po lv n ids)) (fst (snd (pool_alloc po lv n ids))) \<and>
                         diff_ids_valid (fst (pool_alloc po lv n ids))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_alloc_ids_case3:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  id_ids_valid (fst (pool_alloc po lv n ids)) (fst (snd (pool_alloc po lv n ids))) \<and>
  diff_ids_valid (fst (pool_alloc po lv n ids))"
  by auto

lemma pool_alloc_ids_case2:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  id_ids_valid (fst (pool_alloc po lv n ids)) (fst (snd (pool_alloc po lv n ids))) \<and>
  diff_ids_valid (fst (pool_alloc po lv n ids))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n)
  case 0
  then show ?case by linarith
next
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto
  have step: "pool_alloc po lv n ids = pool_alloc po lv (Suc n) ids" using Suc by auto
  {
    assume a00: "snd (snd (snd (alloc ((zerolevelblocklist po) ! (Suc n)) (freelist po) lv ids 0))) = False \<and> (Suc n) < length (zerolevelblocklist po) - 1"
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith  
    ultimately have "id_ids_valid (fst (pool_alloc po lv (Suc n) ids)) (fst (snd (pool_alloc po lv (Suc n) ids))) \<and>
                    diff_ids_valid (fst (pool_alloc po lv (Suc n) ids))"
      using Suc.hyps(1) Suc.prems(1) Suc.prems(2) by blast
  }
  moreover
  have "id_ids_valid (fst (pool_alloc po lv (Suc n) ids)) (fst (snd (pool_alloc po lv (Suc n) ids))) \<and>
       diff_ids_valid (fst (pool_alloc po lv (Suc n) ids))"
    using Suc.prems(1) Suc.prems(2) pool_alloc_ids_case1 pool_alloc_ids_case3 calculation by blast    
  ultimately show ?case using step by auto
qed

lemma inv_ids_pool_alloc:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_ids_valid (fst (pool_alloc po lv n ids)) (fst (snd (pool_alloc po lv n ids))) \<and>
  diff_ids_valid (fst (pool_alloc po lv n ids))"
  apply(cases "lv < 0") apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)")
  using pool_alloc_ids_case1[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_alloc_ids_case3[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  using pool_alloc_ids_case2[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] by simp

lemma idset_subset4_h1:
  "id_ids_valid po ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_alloc po lv n ids))"
proof-
  assume a0: "id_ids_valid po ids"
     and a1: "\<not> lv < 0"
     and a2: "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). id_ids b ids" using a0 id_ids_valid_def by blast 
  have p1: "id_ids (zerolevelblocklist po ! n) ids" using p0 a2 by auto
  let ?re = "let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! n) (freelist po) lv ids 0
              in (po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)"
  have p2: "fst (snd (pool_alloc po lv n ids)) = fst (snd ?re)" apply simp using a2 Let_def by (smt fst_conv snd_conv)
  have p3: "(fst (snd ?re)) = fst (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))"
    unfolding Let_def using a2 by auto
  have ids_sub: "ids \<subseteq> fst (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))"
  proof-
    {assume c0: "lv = 0"
      {assume c10: "get_leaf (zerolevelblocklist po ! n) = True"
        obtain x where c11: "(zerolevelblocklist po ! n) = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (snd (alloc (Leaf x) (freelist po) lv ids 0))) = ids"
            using alloc.simps(1) c0 a10 by auto
          have ?thesis using c11 a11 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (snd (alloc (Leaf x) (freelist po) lv ids 0))) = ids"
            using alloc.simps(1) c0 a20 by auto
          have ?thesis using c11 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }
      moreover
      {assume c20: "get_leaf (zerolevelblocklist po ! n) = False"
        obtain m1 m2 m3 m4 where c21: "(zerolevelblocklist po ! n) = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have a30: "fst (snd (snd (alloc (Node m1 m2 m3 m4) (freelist po) lv ids 0))) = ids"
          using alloc.simps(2) c0 by auto
        have ?thesis using c21 a30 by auto
      }
      ultimately have ?thesis by auto
      then have ?thesis by auto
    }
    moreover
    {assume c1: "lv > 0"
      have ?thesis using idset_subset3 c1 p1 by auto
    }
    ultimately have ?thesis by auto
    then show ?thesis by auto
  qed
  then show ?thesis using p2 p3 by auto
qed

lemma idset_subset4_h3:
  "id_ids_valid po ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_alloc po lv n ids))"
  by auto

lemma idset_subset4_h2:
  "id_ids_valid po ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_alloc po lv n ids))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n)
  case 0
  then show ?case by linarith
next
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto
  have step: "pool_alloc po lv n ids = pool_alloc po lv (Suc n) ids" using Suc by auto
  {
    assume a00: "snd (snd (snd (alloc ((zerolevelblocklist po) ! (Suc n)) (freelist po) lv ids 0))) = False \<and> (Suc n) < length (zerolevelblocklist po) - 1"
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith  
    ultimately have "ids \<subseteq> (fst (snd (pool_alloc po lv (Suc n) ids)))"
      using Suc.hyps(1) Suc.prems(1) Suc.prems(2) by blast
  }
  moreover
  have "ids \<subseteq> (fst (snd (pool_alloc po lv (Suc n) ids)))"
    using Suc.prems(1) Suc.prems(2) idset_subset4_h1 idset_subset4_h3 calculation by blast    
  ultimately show ?case using step by auto
qed

lemma idset_subset4:
  "id_ids_valid po ids \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_alloc po lv n ids))"
  apply(cases "lv < 0") apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)")
  using idset_subset4_h1[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using idset_subset4_h3[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  using idset_subset4_h2[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] by simp

lemma inv_ids_k_mem_pool_alloc_helper1:
  "s \<in> inv_ids \<and> po \<in> set (pools s) \<and> finite (idset s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_ids"
proof-
  assume a0: "s \<in> inv_ids \<and> po \<in> set (pools s) \<and> finite (idset s)"
  hence p0: "\<forall>p \<in> set (pools s). id_ids_valid p (idset s) \<and> diff_ids_valid p"
    by (simp add: inv_ids_def)
  hence p1: "id_ids_valid po (idset s) \<and> diff_ids_valid po"
    by (simp add: a0)
  let ?rpi = "pool_alloc po lv 0 (idset s)"
  have p2: "id_ids_valid (fst ?rpi) (fst (snd ?rpi)) \<and> diff_ids_valid (fst ?rpi)"
     using inv_ids_pool_alloc a0 p1 by blast
  moreover
  have ids_sub: "(idset s) \<subseteq> (fst (snd ?rpi))"
    using idset_subset4 p1 by blast
  from p0 have "\<forall>p \<in> set (pools s). \<forall>b \<in> set (zerolevelblocklist p). id_ids b (idset s) \<and> diff_ids b"
    using id_ids_valid_def diff_ids_valid_def by blast
  then have "\<forall>p \<in> set (pools s). \<forall>b \<in> set (zerolevelblocklist p). id_ids b (fst (snd ?rpi)) \<and> diff_ids b"
    using id_ids_ext ids_sub by auto
  then have p00: "\<forall>p \<in> set (pools s). id_ids_valid p (fst (snd ?rpi)) \<and> diff_ids_valid p"
    using id_ids_valid_def diff_ids_valid_def by blast
  have p3: "\<forall>p \<in> set ((remove1 po (pools s)) @ [fst ?rpi]). id_ids_valid p (fst (snd ?rpi)) \<and> diff_ids_valid p"
    using p00 p2 by auto
  let ?s = "s\<lparr>pools := remove1 po (pools s) @ [fst ?rpi], idset := fst (snd ?rpi)\<rparr>"
  have p4: "?s \<in> inv_ids"
    unfolding inv_ids_def using p3 by auto
  then show "s \<in> inv_ids \<and> po \<in> set (pools s) \<and> finite (idset s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_ids"
    by (smt fst_conv)
qed

lemma inv_ids_k_mem_pool_alloc_helper3:
  "s \<in> inv_ids \<Longrightarrow>
    \<not> snd (snd (let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! 0) (freelist po) lv (idset s) 0; re = snd (snd (snd aa))
                 in if re \<and> zeroli \<noteq> [] then (po\<lparr>zerolevelblocklist := zeroli[0 := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)
                    else if re = False \<and> 0 < length zeroli - 1 then pool_alloc po lv (Suc 0) (idset s) else (po, idset s, False))) \<Longrightarrow>
    schedule (case cur s of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> name po)\<rparr>)) \<in> inv_ids"
proof-
  assume "s \<in> inv_ids"
  hence p0: "\<forall>p \<in> set (pools s). id_ids_valid p (idset s) \<and> diff_ids_valid p"
    using inv_ids_def by blast
  let ?t = "case (cur s) of None \<Rightarrow> s
                    | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := (waitq s)(th \<mapsto> name po)\<rparr>)"
  {
    have p1: "pools s = pools ?t" by (simp add: option.case_eq_if)
    have p2: "idset s = idset ?t" by (simp add: option.case_eq_if) 
    with p0 p1 have p3: "\<forall>p \<in> set (pools ?t). id_ids_valid p (idset ?t) \<and> diff_ids_valid p" by simp
    from p3 have p4: "?t \<in> inv_ids"
      by (simp add: inv_ids_def)
    from p4 have p5: "schedule ?t \<in> inv_ids" by (simp add:inv_ids_schedule)
  }
  then show ?thesis by blast
qed

lemma inv_ids_k_mem_pool_alloc_helper2:
  "s \<in> inv_ids \<and> po \<in> set (pools s) \<and> finite (idset s) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) \<noteq> True \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_ids"
  apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
   prefer 2
   apply blast
  apply(simp add:inv_ids_schedule)
  using inv_ids_k_mem_pool_alloc_helper3 by blast

lemma inv_ids_k_mem_pool_alloc: "s \<in> inv_ids \<and> po \<in> set (pools s) \<and> finite (idset s) \<Longrightarrow> fst (k_mem_pool_alloc s po lv ti) \<in> inv_ids"
proof (induct ti)
  case WAIT
  then show ?case unfolding k_mem_pool_alloc_def
    apply(case_tac "lv < 0")
     apply(simp add:Let_def)
    apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = True")
       apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
      apply(simp add:Let_def)
    using inv_ids_k_mem_pool_alloc_helper1 inv_ids_k_mem_pool_alloc_helper2 snd_conv by auto
  case FOREVER
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_ids\<close> k_mem_pool_alloc_def option.case_eq_if)
  case NO_WAIT
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(2) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_ids\<close> fst_conv k_mem_pool_alloc_def timeout_state_type.distinct(1) timeout_state_type.distinct(5))
qed

lemma inv_ids_free_leaf:
  "id_ids (Leaf x) ids \<and> diff_ids (Leaf x) \<Longrightarrow>
  finite ids \<Longrightarrow>
  fst (snd x) = ALLOC \<Longrightarrow> 
  num = snd (snd x) \<Longrightarrow> 
  id_ids (fst (free (Leaf x) li num ids)) (fst (snd (snd (free (Leaf x) li num ids)))) \<and>
  diff_ids (fst (free (Leaf x) li num ids))"
proof-
  assume a0: "id_ids (Leaf x) ids \<and> diff_ids (Leaf x)"
     and a1: "finite ids"
     and a3: "fst (snd x) = ALLOC"
     and a4: "num = snd (snd x)"
  have p0: "snd (snd x) \<in> ids"
    using a0 id_ids_leaf_node(1) by blast
  have p1: "(fst (free (Leaf x) li num ids)) = (Leaf (fst x, FREE, snd (snd x)))"
    using a3 a4 free.simps(1) by auto
  have p2: "(fst (snd (snd (free (Leaf x) li num ids)))) = ids"
    using a3 a4 free.simps(1) by auto
  have p3: "get_blockid (Leaf (fst x, FREE, snd (snd x))) = snd (snd x)"
    unfolding get_blockid_def by auto
  show ?thesis using p1 p2 p3 p0 a0
    by (simp add: i1 diff1) 
qed

lemma ids_combine:
  "b = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)) \<Longrightarrow>
  ids \<subseteq> (snd (snd (combine b li ids)))"
  unfolding combine_def Let_def using getnewid2_inc by auto

lemma ids_combine2:
  "b = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)) \<Longrightarrow>
  idsets_block (fst (combine b li ids)) \<subseteq> (snd (snd (combine b li ids)))"
  unfolding combine_def Let_def
  apply auto
  using exists_p_getnewid2 fst_conv snd_conv
  by (metis UnCI insertI1) 

lemma ids_combine3:
  "finite ids \<Longrightarrow>
  b = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)) \<Longrightarrow>
  idsets_block (fst (combine b li ids)) \<inter> ids = {}"
  unfolding combine_def Let_def
  apply auto
  using getnewid2_diff by blast

lemma idset_subset5:
  "finite ids \<Longrightarrow>
  ids \<subseteq> fst (snd (snd (free b li num ids)))"
proof(induct b)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  {assume c1: "snd (snd (snd (free b1 li num ids)))"
    let ?c1 = "free b1 li num ids"
    let ?step1 = "if (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node (fst ?c1) b2 b3 b4, fst (snd ?c1), (fst (snd (snd ?c1))), True)"
    have step1: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = fst (snd (snd ?step1))"
      unfolding free.simps(2) Let_def using c1 by auto
    have subsets_b1: "ids \<subseteq> fst (snd (snd ?c1))"
      using Node.hyps(1) Node.prems(1) c1 by auto
    have "fst (snd (snd ?c1)) \<subseteq> fst (snd (snd ?step1))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step1)) = snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "fst (snd (snd ?c1)) \<subseteq> snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)))))"
          using ids_combine ob_case0 by simp 
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step1)) = fst (snd (snd ?c1))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using subsets_b1 step1 by auto
  }
  moreover
  {assume c2: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids)))"
    let ?c2 = "free b2 li num ids"
    let ?step2 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 (fst ?c2) b3 b4, fst (snd ?c2), (fst (snd (snd ?c2))), True)"
    have step2: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = fst (snd (snd ?step2))"
      unfolding free.simps(2) Let_def using c2 by auto
    have subsets_b2: "ids \<subseteq> fst (snd (snd ?c2))"
      using Node.hyps(2) Node.prems(1) c2 by auto
    have "fst (snd (snd ?c2)) \<subseteq> fst (snd (snd ?step2))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step2)) = snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "fst (snd (snd ?c2)) \<subseteq> snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)))))"
          using ids_combine ob_case0 by simp 
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step2)) = fst (snd (snd ?c2))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using subsets_b2 step2 by auto
  }
  moreover
  {assume c3: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids)))"
    let ?c3 = "free b3 li num ids"
    let ?step3 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 (fst ?c3) b4, fst (snd ?c3), (fst (snd (snd ?c3))), True)"
    have step3: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = fst (snd (snd ?step3))"
      unfolding free.simps(2) Let_def using c3 by auto
    have subsets_b3: "ids \<subseteq> fst (snd (snd ?c3))"
      using Node.hyps(3) Node.prems(1) c3 by auto
    have "fst (snd (snd ?c3)) \<subseteq> fst (snd (snd ?step3))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step3)) = snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "fst (snd (snd ?c3)) \<subseteq> snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)))))"
          using ids_combine ob_case0 by simp 
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step3)) = fst (snd (snd ?c3))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using subsets_b3 step3 by auto
  }
  moreover
  {assume c4: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids)))"
    let ?c4 = "free b4 li num ids"
    let ?step4 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 b3 (fst ?c4), fst (snd ?c4), (fst (snd (snd ?c4))), True)"
    have step4: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = fst (snd (snd ?step4))"
      unfolding free.simps(2) Let_def using c4 by auto
    have subsets_b4: "ids \<subseteq> fst (snd (snd ?c4))"
      using Node.hyps(4) Node.prems(1) c4 by auto
    have "fst (snd (snd ?c4)) \<subseteq> fst (snd (snd ?step4))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step4)) = snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "fst (snd (snd ?c4)) \<subseteq> snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)))))"
          using ids_combine ob_case0 by simp 
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step4)) = fst (snd (snd ?c4))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using subsets_b4 step4 by auto
  }
  moreover
  {assume c5: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids))) = False"
    have step5: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = ids"
      unfolding free.simps(2) Let_def using c5 by auto
    then have ?case by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma ids_finite_combine:
  "finite ids \<Longrightarrow>
  b = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  finite (snd (snd (combine b li ids)))"
  unfolding combine_def Let_def
  apply auto
  using exists_p_getnewid2 snd_conv
  by (metis finite.emptyI finite_insert infinite_Un) 

lemma ids_finite_ids2: 
  "finite ids \<Longrightarrow>
  finite (fst (snd (snd (free b li num ids))))"
proof(induct b)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  {assume c1: "snd (snd (snd (free b1 li num ids)))"
    let ?c1 = "free b1 li num ids"
    let ?step1 = "if (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node (fst ?c1) b2 b3 b4, fst (snd ?c1), (fst (snd (snd ?c1))), True)"
    have step1: "free (Node b1 b2 b3 b4) li num ids = ?step1"
      unfolding free.simps(2) Let_def using c1 by auto
    have finite_free_b1: "finite (fst (snd (snd ?c1)))"
      using Node.hyps(1) Node.prems(1) by auto
    have "finite (fst (snd (snd ?step1)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step1)) = snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "finite (snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))))"
          using ids_finite_combine finite_free_b1 ob_case0 by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step1)) = (fst (snd (snd ?c1)))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using finite_free_b1 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step1 by auto
  }
  moreover
  {assume c2: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids)))"
    let ?c2 = "free b2 li num ids"
    let ?step2 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 (fst ?c2) b3 b4, fst (snd ?c2), (fst (snd (snd ?c2))), True)"
    have step2: "free (Node b1 b2 b3 b4) li num ids = ?step2"
      unfolding free.simps(2) Let_def using c2 by auto
    have finite_free_b2: "finite (fst (snd (snd ?c2)))"
      using Node.hyps(2) Node.prems(1) by auto
    have "finite (fst (snd (snd ?step2)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step2)) = snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "finite (snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))))"
          using ids_finite_combine finite_free_b2 ob_case0 by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step2)) = (fst (snd (snd ?c2)))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using finite_free_b2 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step2 by auto
  }
  moreover
  {assume c3: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids)))"
    let ?c3 = "free b3 li num ids"
    let ?step3 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 (fst ?c3) b4, fst (snd ?c3), (fst (snd (snd ?c3))), True)"
    have step3: "free (Node b1 b2 b3 b4) li num ids = ?step3"
      unfolding free.simps(2) Let_def using c3 by auto
    have finite_free_b3: "finite (fst (snd (snd ?c3)))"
      using Node.hyps(3) Node.prems(1) by auto
    have "finite (fst (snd (snd ?step3)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step3)) = snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "finite (snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))))"
          using ids_finite_combine finite_free_b3 ob_case0 by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step3)) = (fst (snd (snd ?c3)))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using finite_free_b3 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step3 by auto
  }
  moreover
  {assume c4: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids)))"
    let ?c4 = "free b4 li num ids"
    let ?step4 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 b3 (fst ?c4), fst (snd ?c4), (fst (snd (snd ?c4))), True)"
    have step4: "free (Node b1 b2 b3 b4) li num ids = ?step4"
      unfolding free.simps(2) Let_def using c4 by auto
    have finite_free_b4: "finite (fst (snd (snd ?c4)))"
      using Node.hyps(4) Node.prems(1) by auto
    have "finite (fst (snd (snd ?step4)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step4)) = snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "finite (snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))))"
          using ids_finite_combine finite_free_b4 ob_case0 by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step4)) = (fst (snd (snd ?c4)))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using finite_free_b4 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step4 by auto
  }
  moreover
  {assume c5: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids))) = False"
    have step5: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = ids"
      unfolding free.simps(2) Let_def using c5 by auto
    then have ?case using Node.prems by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma ids_overlap_empty3:
  "idsets_block oth \<subseteq> ids \<Longrightarrow>
  idsets_block b \<subseteq> ids \<Longrightarrow>
  idsets_block oth \<inter> idsets_block b = {} \<Longrightarrow>
  finite ids \<Longrightarrow>
  idsets_block oth \<inter> idsets_block (fst (free b li num ids)) = {}"
proof(induct b arbitrary: li num ids oth)
  case (Leaf x)
  then show ?case by auto
next
  case (Node b1 b2 b3 b4)
  have idsets_b1: "idsets_block b1 \<subseteq> ids"
    using Node.prems(2) by auto
  have idsets_b2: "idsets_block b2 \<subseteq> ids"
    using Node.prems(2) by auto
  have idsets_b3: "idsets_block b3 \<subseteq> ids"
    using Node.prems(2) by auto
  have idsets_b4: "idsets_block b4 \<subseteq> ids"
    using Node.prems(2) by auto
  have overlap_b1: "idsets_block oth \<inter> idsets_block b1 = {}"
    using Node.prems(3) by auto
  have overlap_b2: "idsets_block oth \<inter> idsets_block b2 = {}"
    using Node.prems(3) by auto
  have overlap_b3: "idsets_block oth \<inter> idsets_block b3 = {}"
    using Node.prems(3) by auto
  have overlap_b4: "idsets_block oth \<inter> idsets_block b4 = {}"
    using Node.prems(3) by auto

  {assume c1: "snd (snd (snd (free b1 li num ids)))"
    let ?c1 = "free b1 li num ids"
    let ?step1 = "if (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node (fst ?c1) b2 b3 b4, fst (snd ?c1), (fst (snd (snd ?c1))), True)"
    have step1: "free (Node b1 b2 b3 b4) li num ids = ?step1"
      unfolding free.simps(2) Let_def using c1 by auto
    have idsets_free_b1: "idsets_block (fst ?c1) \<inter> idsets_block oth = {}"
      using Node.hyps(1) Node.prems(1) idsets_b1 overlap_b1 Node.prems(4) by blast
    have idsets_free_node1: "idsets_block (Node (fst ?c1) b2 b3 b4) \<inter> idsets_block oth = {}"
      using idsets_free_b1 overlap_b2 overlap_b3 overlap_b4 idsets_block.simps(2) by auto
    have "idsets_block (fst ?step1) \<inter> idsets_block oth = {}"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step1 = fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have subset_b1: "ids \<subseteq> (fst (snd (snd ?c1)))"
          using idset_subset5 Node.prems(4) by auto
        have subset_oth: "idsets_block oth \<subseteq> (fst (snd (snd ?c1)))"
          using subset_b1 Node.prems(1) by auto
        have "idsets_block (fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))) \<inter> (fst (snd (snd ?c1))) = {}"
          using ids_combine3 Node.prems(4) ids_finite_ids2 ob_case0 by auto
        then have "idsets_block (fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))) \<inter> idsets_block oth = {}"
          using subset_oth by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (?step1) = (Node (fst ?c1) b2 b3 b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using idsets_free_node1 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step1 by auto
  }
  moreover
  {assume c2: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids)))"
    let ?c2 = "free b2 li num ids"
    let ?step2 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 (fst ?c2) b3 b4, fst (snd ?c2), (fst (snd (snd ?c2))), True)"
    have step2: "free (Node b1 b2 b3 b4) li num ids = ?step2"
      unfolding free.simps(2) Let_def using c2 by auto
    have idsets_free_b2: "idsets_block (fst ?c2) \<inter> idsets_block oth = {}"
      using Node.hyps(2) Node.prems(1) idsets_b2 overlap_b2 Node.prems(4) by blast
    have idsets_free_node2: "idsets_block (Node b1 (fst ?c2) b3 b4) \<inter> idsets_block oth = {}"
      using idsets_free_b2 overlap_b1 overlap_b3 overlap_b4 idsets_block.simps(2) by auto
    have "idsets_block (fst ?step2) \<inter> idsets_block oth = {}"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step2 = fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have subset_b1: "ids \<subseteq> (fst (snd (snd ?c2)))"
          using idset_subset5 Node.prems(4) by auto
        have subset_oth: "idsets_block oth \<subseteq> (fst (snd (snd ?c2)))"
          using subset_b1 Node.prems(1) by auto
        have "idsets_block (fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))) \<inter> (fst (snd (snd ?c2))) = {}"
          using ids_combine3 Node.prems(4) ids_finite_ids2 ob_case0 by auto
        then have "idsets_block (fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))) \<inter> idsets_block oth = {}"
          using subset_oth by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (?step2) = (Node b1 (fst ?c2) b3 b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using idsets_free_node2 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step2 by auto
  }
  moreover
  {assume c3: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids)))"
    let ?c3 = "free b3 li num ids"
    let ?step3 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 (fst ?c3) b4, fst (snd ?c3), (fst (snd (snd ?c3))), True)"
    have step3: "free (Node b1 b2 b3 b4) li num ids = ?step3"
      unfolding free.simps(2) Let_def using c3 by auto
    have idsets_free_b3: "idsets_block (fst ?c3) \<inter> idsets_block oth = {}"
      using Node.hyps(3) Node.prems(1) idsets_b3 overlap_b3 Node.prems(4) by blast
    have idsets_free_node3: "idsets_block (Node b1 b2 (fst ?c3) b4) \<inter> idsets_block oth = {}"
      using idsets_free_b3 overlap_b1 overlap_b2 overlap_b4 idsets_block.simps(2) by auto
    have "idsets_block (fst ?step3) \<inter> idsets_block oth = {}"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step3 = fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have subset_b1: "ids \<subseteq> (fst (snd (snd ?c3)))"
          using idset_subset5 Node.prems(4) by auto
        have subset_oth: "idsets_block oth \<subseteq> (fst (snd (snd ?c3)))"
          using subset_b1 Node.prems(1) by auto
        have "idsets_block (fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))) \<inter> (fst (snd (snd ?c3))) = {}"
          using ids_combine3 Node.prems(4) ids_finite_ids2 ob_case0 by auto
        then have "idsets_block (fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))) \<inter> idsets_block oth = {}"
          using subset_oth by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (?step3) = (Node b1 b2 (fst ?c3) b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using idsets_free_node3 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step3 by auto
  }
  moreover
  {assume c4: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids)))"
    let ?c4 = "free b4 li num ids"
    let ?step4 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 b3 (fst ?c4), fst (snd ?c4), (fst (snd (snd ?c4))), True)"
    have step4: "free (Node b1 b2 b3 b4) li num ids = ?step4"
      unfolding free.simps(2) Let_def using c4 by auto
    have idsets_free_b4: "idsets_block (fst ?c4) \<inter> idsets_block oth = {}"
      using Node.hyps(4) Node.prems(1) idsets_b4 overlap_b4 Node.prems(4) by blast
    have idsets_free_node4: "idsets_block (Node b1 b2 b3 (fst ?c4)) \<inter> idsets_block oth = {}"
      using idsets_free_b4 overlap_b1 overlap_b2 overlap_b3 idsets_block.simps(2) by auto
    have "idsets_block (fst ?step4) \<inter> idsets_block oth = {}"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step4 = fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have subset_b1: "ids \<subseteq> (fst (snd (snd ?c4)))"
          using idset_subset5 Node.prems(4) by auto
        have subset_oth: "idsets_block oth \<subseteq> (fst (snd (snd ?c4)))"
          using subset_b1 Node.prems(1) by auto
        have "idsets_block (fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))) \<inter> (fst (snd (snd ?c4))) = {}"
          using ids_combine3 Node.prems(4) ids_finite_ids2 ob_case0 by auto
        then have "idsets_block (fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))) \<inter> idsets_block oth = {}"
          using subset_oth by auto
        then have ?thesis using step_case0 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (?step4) = (Node b1 b2 b3 (fst ?c4))"
          unfolding free.simps(2) Let_def using case1 by auto
        then have ?thesis using idsets_free_node4 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed
    then have ?case using step4 by auto
  }
  moreover
  {assume c5: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids))) = False"
    have step5: "fst (free (Node b1 b2 b3 b4) li num ids) = (Node b1 b2 b3 b4)"
      unfolding free.simps(2) Let_def using c5 by auto
    then have ?case using Node.prems(3) by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma inv_ids_free:
  "id_ids b ids \<and> diff_ids b \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (free b li num ids))) = True \<Longrightarrow>
  id_ids (fst (free b li num ids)) (fst (snd (snd (free b li num ids)))) \<and>
  diff_ids (fst (free b li num ids))"
proof(induct b)
  case (Leaf x)
  then show ?case
    apply auto
    using inv_ids_free_leaf by auto
next
  case (Node b1 b2 b3 b4)
  have ids_b1: "id_ids b1 ids"
    using Node.prems(1) id_ids_leaf_node(2) by auto
  have ids_b2: "id_ids b2 ids"
    using Node.prems(1) id_ids_leaf_node(2) by auto
  have ids_b3: "id_ids b3 ids"
    using Node.prems(1) id_ids_leaf_node(2) by auto
  have ids_b4: "id_ids b4 ids"
    using Node.prems(1) id_ids_leaf_node(2) by auto
  have diff_b1: "diff_ids b1 "
    using Node.prems(1) diff_ids_leaf_node(2) by auto
  have diff_b2: "diff_ids b2 "
    using Node.prems(1) diff_ids_leaf_node(2) by auto
  have diff_b3: "diff_ids b3 "
    using Node.prems(1) diff_ids_leaf_node(2) by auto
  have diff_b4: "diff_ids b4 "
    using Node.prems(1) diff_ids_leaf_node(2) by auto
  have diff_ab: "idsets_block b1 \<inter> idsets_block b2 = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ac: "idsets_block b1 \<inter> idsets_block b3 = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_ad: "idsets_block b1 \<inter> idsets_block b4 = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bc: "idsets_block b2 \<inter> idsets_block b3 = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_bd: "idsets_block b2 \<inter> idsets_block b4 = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  have diff_cd: "idsets_block b3 \<inter> idsets_block b4 = {}"
    using Node.prems(1) diff_ids_leaf_node(2) by blast
  {assume c1: "snd (snd (snd (free b1 li num ids)))"
    let ?c1 = "free b1 li num ids"
    let ?step1 = "if (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node (fst ?c1) b2 b3 b4, fst (snd ?c1), (fst (snd (snd ?c1))), True)"
    have step1: "free (Node b1 b2 b3 b4) li num ids = ?step1"
      unfolding free.simps(2) Let_def using c1 by auto
    have id_ids_free_b1: "id_ids (fst ?c1) (fst (snd (snd ?c1)))"
      using Node.hyps(1) ids_b1 diff_b1 Node.prems(2) c1 by auto
    have subset_b1: "ids \<subseteq> (fst (snd (snd ?c1)))"
      using idset_subset5 Node.prems(2) by auto
    have id_ids_free_b1_b2: "id_ids b2 (fst (snd (snd ?c1)))"
      using ids_b2 subset_b1 id_ids_ext by auto
    have id_ids_free_b1_b3: "id_ids b3 (fst (snd (snd ?c1)))"
      using ids_b3 subset_b1 id_ids_ext by auto
    have id_ids_free_b1_b4: "id_ids b4 (fst (snd (snd ?c1)))"
      using ids_b4 subset_b1 id_ids_ext by auto
    have id_ids_free_node1: "id_ids (Node (fst ?c1) b2 b3 b4) (fst (snd (snd ?c1)))"
      using id_ids_free_b1 id_ids_free_b1_b2 id_ids_free_b1_b3 id_ids_free_b1_b4 by (simp add: i2)
    have id_ids_combine_b1: "id_ids (fst ?step1) (fst (snd (snd ?step1)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step1)) = snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        have step_case01: "fst ?step1 = fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "idsets_block (fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))) \<subseteq> snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)))))"
          using ids_combine2 ob_case0 by auto
        then have "id_ids (fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))) (snd (snd (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))))"
          using idsets_block_id_ids2 by auto
        then have ?thesis using step_case0 step_case01 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step1)) = fst (snd (snd ?c1))"
          unfolding free.simps(2) Let_def using case1 by auto
        have step_case11: "fst ?step1 = (Node (fst ?c1) b2 b3 b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using id_ids_free_node1 step_case1 step_case11 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have diff_ids_free_b1: "diff_ids (fst ?c1)"
      using Node.hyps(1) ids_b1 diff_b1 Node.prems(2) c1 by auto
    have diff_free_b1_b2: "idsets_block (fst ?c1) \<inter> idsets_block b2 = {}"
      using ids_overlap_empty3 ids_b2 ids_b1 diff_ab Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b1_b3: "idsets_block (fst ?c1) \<inter> idsets_block b3 = {}"
      using ids_overlap_empty3 ids_b3 ids_b1 diff_ac Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b1_b4: "idsets_block (fst ?c1) \<inter> idsets_block b4 = {}"
      using ids_overlap_empty3 ids_b4 ids_b1 diff_ad Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_ids_free_node1: "diff_ids (Node (fst ?c1) b2 b3 b4)"
      using diff_ids_free_b1 diff_b2 diff_b3 diff_b4
      using diff_free_b1_b2 diff_free_b1_b3 diff_free_b1_b4 diff_bc diff_bd diff_cd
      by (simp add: diff2)
    have diff_ids_combine_b1: "diff_ids (fst ?step1)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step1 = fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "get_leaf (fst (combine (Node (fst ?c1) b2 b3 b4) (fst (snd ?c1)) (fst (snd (snd ?c1)))))"
          unfolding combine_def Let_def using ob_case0 by auto
        then have ?thesis using step_case0
          by (smt diff1 get_leaf.simps(2) tree.exhaust) 
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node (fst ?c1) b2 b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step1 = (Node (fst ?c1) b2 b3 b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using diff_ids_free_node1 step_case1 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have ?case using id_ids_combine_b1 diff_ids_combine_b1 step1 by auto
  }
  moreover
  {assume c2: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids)))"
    let ?c2 = "free b2 li num ids"
    let ?step2 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 (fst ?c2) b3 b4, fst (snd ?c2), (fst (snd (snd ?c2))), True)"
    have step2: "free (Node b1 b2 b3 b4) li num ids = ?step2"
      unfolding free.simps(2) Let_def using c2 by auto
    have id_ids_free_b2: "id_ids (fst ?c2) (fst (snd (snd ?c2)))"
      using Node.hyps(2) ids_b2 diff_b2 Node.prems(2) c2 by auto
    have subset_b2: "ids \<subseteq> (fst (snd (snd ?c2)))"
      using idset_subset5 Node.prems(2) by auto
    have id_ids_free_b2_b1: "id_ids b1 (fst (snd (snd ?c2)))"
      using ids_b1 subset_b2 id_ids_ext by auto
    have id_ids_free_b2_b3: "id_ids b3 (fst (snd (snd ?c2)))"
      using ids_b3 subset_b2 id_ids_ext by auto
    have id_ids_free_b2_b4: "id_ids b4 (fst (snd (snd ?c2)))"
      using ids_b4 subset_b2 id_ids_ext by auto
    have id_ids_free_node2: "id_ids (Node b1 (fst ?c2) b3 b4) (fst (snd (snd ?c2)))"
      using id_ids_free_b2 id_ids_free_b2_b1 id_ids_free_b2_b3 id_ids_free_b2_b4 by (simp add: i2)
    have id_ids_combine_b2: "id_ids (fst ?step2) (fst (snd (snd ?step2)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step2)) = snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        have step_case01: "fst ?step2 = fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "idsets_block (fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))) \<subseteq> snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)))))"
          using ids_combine2 ob_case0 by auto
        then have "id_ids (fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))) (snd (snd (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))))"
          using idsets_block_id_ids2 by auto
        then have ?thesis using step_case0 step_case01 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step2)) = fst (snd (snd ?c2))"
          unfolding free.simps(2) Let_def using case1 by auto
        have step_case11: "fst ?step2 = (Node b1 (fst ?c2) b3 b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using id_ids_free_node2 step_case1 step_case11 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have diff_ids_free_b2: "diff_ids (fst ?c2)"
      using Node.hyps(2) ids_b2 diff_b2 Node.prems(2) c2 by auto
    have diff_free_b2_b1: "idsets_block (fst ?c2) \<inter> idsets_block b1 = {}"
      using ids_overlap_empty3 ids_b1 ids_b2 diff_ab Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b2_b3: "idsets_block (fst ?c2) \<inter> idsets_block b3 = {}"
      using ids_overlap_empty3 ids_b3 ids_b2 diff_bc Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b2_b4: "idsets_block (fst ?c2) \<inter> idsets_block b4 = {}"
      using ids_overlap_empty3 ids_b4 ids_b2 diff_bd Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_ids_free_node2: "diff_ids (Node b1 (fst ?c2) b3 b4)"
      using diff_ids_free_b2 diff_b1 diff_b3 diff_b4
      using diff_free_b2_b1 diff_free_b2_b3 diff_free_b2_b4 diff_ac diff_ad diff_cd
      by (simp add: diff2 inf_commute)
    have diff_ids_combine_b2: "diff_ids (fst ?step2)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step2 = fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "get_leaf (fst (combine (Node b1 (fst ?c2) b3 b4) (fst (snd ?c2)) (fst (snd (snd ?c2)))))"
          unfolding combine_def Let_def using ob_case0 by auto
        then have ?thesis using step_case0
          by (smt diff1 get_leaf.simps(2) tree.exhaust) 
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 (fst ?c2) b3 b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step2 = (Node b1 (fst ?c2) b3 b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using diff_ids_free_node2 step_case1 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have ?case using id_ids_combine_b2 diff_ids_combine_b2 step2 by auto
  }
  moreover
  {assume c3: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids)))"
    let ?c3 = "free b3 li num ids"
    let ?step3 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 (fst ?c3) b4, fst (snd ?c3), (fst (snd (snd ?c3))), True)"
    have step3: "free (Node b1 b2 b3 b4) li num ids = ?step3"
      unfolding free.simps(2) Let_def using c3 by auto
    have id_ids_free_b3: "id_ids (fst ?c3) (fst (snd (snd ?c3)))"
      using Node.hyps(3) ids_b3 diff_b3 Node.prems(2) c3 by auto
    have subset_b3: "ids \<subseteq> (fst (snd (snd ?c3)))"
      using idset_subset5 Node.prems(2) by auto
    have id_ids_free_b3_b1: "id_ids b1 (fst (snd (snd ?c3)))"
      using ids_b1 subset_b3 id_ids_ext by auto
    have id_ids_free_b3_b2: "id_ids b2 (fst (snd (snd ?c3)))"
      using ids_b2 subset_b3 id_ids_ext by auto
    have id_ids_free_b3_b4: "id_ids b4 (fst (snd (snd ?c3)))"
      using ids_b4 subset_b3 id_ids_ext by auto
    have id_ids_free_node3: "id_ids (Node b1 b2 (fst ?c3) b4) (fst (snd (snd ?c3)))"
      using id_ids_free_b3 id_ids_free_b3_b1 id_ids_free_b3_b2 id_ids_free_b3_b4 by (simp add: i2)
    have id_ids_combine_b3: "id_ids (fst ?step3) (fst (snd (snd ?step3)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step3)) = snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        have step_case01: "fst ?step3 = fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "idsets_block (fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))) \<subseteq> snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)))))"
          using ids_combine2 ob_case0 by auto
        then have "id_ids (fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))) (snd (snd (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))))"
          using idsets_block_id_ids2 by auto
        then have ?thesis using step_case0 step_case01 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step3)) = fst (snd (snd ?c3))"
          unfolding free.simps(2) Let_def using case1 by auto
        have step_case11: "fst ?step3 = (Node b1 b2 (fst ?c3) b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using id_ids_free_node3 step_case1 step_case11 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have diff_ids_free_b3: "diff_ids (fst ?c3)"
      using Node.hyps(3) ids_b3 diff_b3 Node.prems(2) c3 by auto
    have diff_free_b3_b1: "idsets_block (fst ?c3) \<inter> idsets_block b1 = {}"
      using ids_overlap_empty3 ids_b1 ids_b3 diff_ac Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b3_b2: "idsets_block (fst ?c3) \<inter> idsets_block b2 = {}"
      using ids_overlap_empty3 ids_b2 ids_b3 diff_bc Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b3_b4: "idsets_block (fst ?c3) \<inter> idsets_block b4 = {}"
      using ids_overlap_empty3 ids_b4 ids_b3 diff_cd Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_ids_free_node3: "diff_ids (Node b1 b2 (fst ?c3) b4)"
      using diff_ids_free_b3 diff_b1 diff_b2 diff_b4
      using diff_free_b3_b1 diff_free_b3_b2 diff_free_b3_b4 diff_ab diff_ad diff_bd
      by (simp add: diff2 inf_commute)
    have diff_ids_combine_b3: "diff_ids (fst ?step3)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step3 = fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "get_leaf (fst (combine (Node b1 b2 (fst ?c3) b4) (fst (snd ?c3)) (fst (snd (snd ?c3)))))"
          unfolding combine_def Let_def using ob_case0 by auto
        then have ?thesis using step_case0
          by (smt diff1 get_leaf.simps(2) tree.exhaust) 
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 (fst ?c3) b4) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step3 = (Node b1 b2 (fst ?c3) b4)"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using diff_ids_free_node3 step_case1 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have ?case using id_ids_combine_b3 diff_ids_combine_b3 step3 by auto
  }
  moreover
  {assume c4: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids)))"
    let ?c4 = "free b4 li num ids"
    let ?step4 = "if (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))
                  then (let re = combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)));
                            node = fst re;
                            freeset = fst (snd re);
                            nids = snd (snd re) in (node, freeset, nids, True))
                  else (Node b1 b2 b3 (fst ?c4), fst (snd ?c4), (fst (snd (snd ?c4))), True)"
    have step4: "free (Node b1 b2 b3 b4) li num ids = ?step4"
      unfolding free.simps(2) Let_def using c4 by auto
    have id_ids_free_b4: "id_ids (fst ?c4) (fst (snd (snd ?c4)))"
      using Node.hyps(4) ids_b4 diff_b4 Node.prems(2) c4 by auto
    have subset_b4: "ids \<subseteq> (fst (snd (snd ?c4)))"
      using idset_subset5 Node.prems(2) by auto
    have id_ids_free_b4_b1: "id_ids b1 (fst (snd (snd ?c4)))"
      using ids_b1 subset_b4 id_ids_ext by auto
    have id_ids_free_b4_b2: "id_ids b2 (fst (snd (snd ?c4)))"
      using ids_b2 subset_b4 id_ids_ext by auto
    have id_ids_free_b4_b3: "id_ids b3 (fst (snd (snd ?c4)))"
      using ids_b3 subset_b4 id_ids_ext by auto
    have id_ids_free_node4: "id_ids (Node b1 b2 b3 (fst ?c4)) (fst (snd (snd ?c4)))"
      using id_ids_free_b4 id_ids_free_b4_b1 id_ids_free_b4_b2 id_ids_free_b4_b3 by (simp add: i2)
    have id_ids_combine_b4: "id_ids (fst ?step4) (fst (snd (snd ?step4)))"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst (snd (snd ?step4)) = snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)))))"
          unfolding free.simps(2) Let_def using case0 by auto
        have step_case01: "fst ?step4 = fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "idsets_block (fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))) \<subseteq> snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)))))"
          using ids_combine2 ob_case0 by auto
        then have "id_ids (fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))) (snd (snd (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))))"
          using idsets_block_id_ids2 by auto
        then have ?thesis using step_case0 step_case01 by auto
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst (snd (snd ?step4)) = fst (snd (snd ?c4))"
          unfolding free.simps(2) Let_def using case1 by auto
        have step_case11: "fst ?step4 = (Node b1 b2 b3 (fst ?c4))"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using id_ids_free_node4 step_case1 step_case11 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have diff_ids_free_b4: "diff_ids (fst ?c4)"
      using Node.hyps(4) ids_b4 diff_b4 Node.prems(2) c4 by auto
    have diff_free_b4_b1: "idsets_block (fst ?c4) \<inter> idsets_block b1 = {}"
      using ids_overlap_empty3 ids_b1 ids_b4 diff_ad Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b4_b2: "idsets_block (fst ?c4) \<inter> idsets_block b2 = {}"
      using ids_overlap_empty3 ids_b2 ids_b4 diff_bd Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_free_b4_b3: "idsets_block (fst ?c4) \<inter> idsets_block b3 = {}"
      using ids_overlap_empty3 ids_b3 ids_b4 diff_cd Node.prems(2) idsets_block_id_ids
      by (simp add: inf_commute) 
    have diff_ids_free_node4: "diff_ids (Node b1 b2 b3 (fst ?c4))"
      using diff_ids_free_b4 diff_b1 diff_b2 diff_b3
      using diff_free_b4_b1 diff_free_b4_b2 diff_free_b4_b3 diff_ab diff_ac diff_bc
      by (simp add: diff2 inf_commute)

    have diff_ids_combine_b4: "diff_ids (fst ?step4)"
    proof-
      {assume case0: "(\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case0: "fst ?step4 = fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4))))"
          unfolding free.simps(2) Let_def using case0 by auto
        obtain la lb lc ld xa xb xc xd where ob_case0: "(Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd))"
          using case0 by auto
        have "get_leaf (fst (combine (Node b1 b2 b3 (fst ?c4)) (fst (snd ?c4)) (fst (snd (snd ?c4)))))"
          unfolding combine_def Let_def using ob_case0 by auto
        then have ?thesis using step_case0
          by (smt diff1 get_leaf.simps(2) tree.exhaust) 
      }moreover
      {assume case1: "\<not> (\<exists>la lb lc ld xa xb xc xd. (Node b1 b2 b3 (fst ?c4)) = Node (Leaf (la, FREE, xa)) (Leaf (lb, FREE, xb)) (Leaf (lc, FREE, xc)) (Leaf (ld, FREE, xd)))"
        have step_case1: "fst ?step4 = (Node b1 b2 b3 (fst ?c4))"
          unfolding free.simps(2) Let_def using case1 by auto
        have ?thesis using diff_ids_free_node4 step_case1 by auto
      }
      ultimately have ?thesis by blast
      then show ?thesis by auto
    qed

    have ?case using id_ids_combine_b4 diff_ids_combine_b4 step4 by auto
  }
  moreover
  {assume c5: "snd (snd (snd (free b1 li num ids))) = False \<and>
               snd (snd (snd (free b2 li num ids))) = False \<and>
               snd (snd (snd (free b3 li num ids))) = False \<and>
               snd (snd (snd (free b4 li num ids))) = False"
    have step5: "fst (free (Node b1 b2 b3 b4) li num ids) = (Node b1 b2 b3 b4)"
      unfolding free.simps(2) Let_def using c5 by auto
    have step55: "fst (snd (snd (free (Node b1 b2 b3 b4) li num ids))) = ids"
      unfolding free.simps(2) Let_def using c5 by auto
    have ?case using step5 step55 Node.prems(1) by auto
  }
  ultimately have ?case by blast
  then show ?case by auto
qed

lemma pool_free_ids_case1:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  id_ids_valid (fst (pool_free po num n ids)) (fst (snd (pool_free po num n ids))) \<and>
  diff_ids_valid (fst (pool_free po num n ids))"
proof-
  assume a0: "id_ids_valid po ids \<and> diff_ids_valid po"
     and a1: "finite ids"
     and a2: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). id_ids b ids \<and> diff_ids b"
    using a0 id_ids_valid_def diff_ids_valid_def by blast
  have p1: "id_ids (zerolevelblocklist po ! n) ids \<and> diff_ids (zerolevelblocklist po ! n)" using p0 a2 by auto
  have p2: "id_ids (fst (free (zerolevelblocklist po ! n) (freelist po) num ids)) (fst (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids)))) \<and>
           diff_ids (fst (free (zerolevelblocklist po ! n) (freelist po) num ids))"
    using p1 a1 a2 inv_ids_free by auto
  let ?t = "let zeroli = zerolevelblocklist po; aa = free (zeroli ! n) (freelist po) num ids
            in (po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)"
  {
    have p3: "fst (pool_free po num n ids) = fst ?t" apply simp using a2 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist (fst ?t) ! n) = fst (free (zerolevelblocklist po ! n) (freelist po) num ids)"
      unfolding Let_def using a2 by auto
    have p5: "fst (snd ?t) = fst (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids)))"
      unfolding Let_def using a2 by auto
    then have p6: "id_ids (zerolevelblocklist (fst ?t) ! n) (fst (snd ?t)) \<and> diff_ids (zerolevelblocklist (fst ?t) ! n)"
      using p2 p4 p5 unfolding Let_def by auto
    have ids_sub: "ids \<subseteq> (fst (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))))"
      using idset_subset5 a1 by auto
    with p0 have p00: "\<forall>b \<in> set (zerolevelblocklist po). id_ids b (fst (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids)))) \<and>
                                                         diff_ids b"
      using id_ids_ext by auto
    with p6 have p7: "\<forall>b \<in> set (zerolevelblocklist (fst ?t)). id_ids b (fst (snd ?t)) \<and> diff_ids b"
      unfolding Let_def apply auto
      using p2 set_update_subset_insert apply fastforce
      by (metis in_set_conv_nth length_list_update nth_list_update_neq)
    have p8: "id_ids_valid (fst ?t) (fst (snd ?t)) \<and> diff_ids_valid (fst ?t)"
      unfolding id_ids_valid_def diff_ids_valid_def using p7 by auto
    with p3 p4 p5 have p9: "id_ids_valid (fst (pool_free po num n ids)) (fst (snd (pool_free po num n ids))) \<and>
                           diff_ids_valid (fst (pool_free po num n ids))"
      by (simp add: a2) 
  }
  then show ?thesis by auto
qed

lemma pool_free_ids_case3:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  id_ids_valid (fst (pool_free po num n ids)) (fst (snd (pool_free po num n ids))) \<and>
  diff_ids_valid (fst (pool_free po num n ids))"
  by auto

lemma pool_free_ids_case2:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  id_ids_valid (fst (pool_free po num n ids)) (fst (snd (pool_free po num n ids))) \<and>
  diff_ids_valid (fst (pool_free po num n ids))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith 
next 
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto     
  have step: "pool_free po num n ids = pool_free po num (Suc n) ids" using Suc by auto
  { 
    assume a00: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1) "
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith   
    ultimately have "id_ids_valid (fst (pool_free po num (Suc n) ids)) (fst (snd (pool_free po num (Suc n) ids))) \<and>
                    diff_ids_valid (fst (pool_free po num (Suc n) ids))"
      using Suc.hyps(1) Suc.prems(1) Suc.prems(2) pool_free_ids_case1 pool_free_ids_case3 by blast
  }    
  moreover 
  have "id_ids_valid (fst (pool_free po num (Suc n) ids)) (fst (snd (pool_free po num (Suc n) ids))) \<and>
       diff_ids_valid (fst (pool_free po num (Suc n) ids))"
    using Suc.prems(4) calculation by blast 
  ultimately show ?case using step by auto
qed

lemma inv_ids_pool_free:
  "id_ids_valid po ids \<and> diff_ids_valid po \<Longrightarrow>
  finite ids \<Longrightarrow>
  id_ids_valid (fst (pool_free po num n ids)) (fst (snd (pool_free po num n ids))) \<and>
  diff_ids_valid (fst (pool_free po num n ids))"
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)")
  using pool_free_ids_case1[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_free_ids_case3[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  using pool_free_ids_case2[where po = "po" and num = "num" and n = "n" and ids = "ids"] by simp

lemma idset_subset6_h1:
  "finite ids \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_free po num n ids))"
proof-
  assume a0: "finite ids"
     and a1: "snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)"
  have p0: "fst (snd (pool_free po num n ids)) = fst (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))"
    using pool_free.simps Let_def a1
    by (smt fst_conv snd_conv)
  have p1: "ids \<subseteq> (fst (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))))"
    using idset_subset5 a0 by auto
  then show ?thesis using p0 p1 by auto
qed

lemma idset_subset6_h3:
  "finite ids \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_free po num n ids))"
  by auto

lemma idset_subset6_h2:
  "finite ids \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_free po num n ids))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith 
next 
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto     
  have step: "pool_free po num n ids = pool_free po num (Suc n) ids" using Suc by auto
  { 
    assume a00: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1) "
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith   
    ultimately have "ids \<subseteq> (fst (snd (pool_free po num (Suc n) ids)))"
      using idset_subset6_h1 idset_subset6_h3 by (meson Suc.hyps(1) Suc.prems(1))
  }    
  moreover 
  have "ids \<subseteq> (fst (snd (pool_free po num (Suc n) ids)))"
    using Suc.prems(3) calculation by blast 
  ultimately show ?case using step by auto
qed

lemma idset_subset6:
  "finite ids \<Longrightarrow>
  ids \<subseteq> fst (snd (pool_free po num n ids))"
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)")
  using idset_subset6_h1[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using idset_subset6_h3[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  using idset_subset6_h2[where po = "po" and num = "num" and n = "n" and ids = "ids"] by simp

lemma id_ids_ext2:
  "ids \<subseteq> ids' \<Longrightarrow>
  id_ids_valid p ids \<Longrightarrow>
  id_ids_valid p ids'"
  unfolding id_ids_valid_def using id_ids_ext by auto

lemma inv_ids_k_mem_pool_free: "po \<in> set (pools s) \<and> s \<in> inv_ids \<and> finite (idset s) \<Longrightarrow> fst (k_mem_pool_free s po num) \<in> inv_ids"
proof-
  assume a0: "po \<in> set (pools s) \<and> s \<in> inv_ids \<and> finite (idset s)"
  hence p0: "\<forall>p \<in> set (pools s). id_ids_valid p (idset s) \<and> diff_ids_valid p" unfolding inv_ids_def by auto
  from a0 p0 have p1: "id_ids_valid po (idset s) \<and> diff_ids_valid po" by simp 
  let ?re = "pool_free po num 0 (idset s)"
  from p1 have p2: "id_ids_valid (fst ?re) (fst (snd ?re)) \<and> diff_ids_valid (fst ?re)"
    using inv_ids_pool_free[where po = "po" and num = "num" and n = 0 and ids = "idset s"] a0 by auto
  have s_in_re: "(idset s) \<subseteq> (fst (snd ?re))"
    using idset_subset6 a0 by blast
  let ?t = "fst (k_mem_pool_free s po num)"
  {assume c0: "snd (snd (pool_free po num 0 (idset s)))"
    have idset_change: "(idset ?t) = (fst (snd ?re))"
      unfolding k_mem_pool_free_def Let_def
      apply(case_tac "{t. (waitq s) t = Some (name po)} \<noteq> {}")
      using c0 apply auto[1]
      using c0 by auto
    have pool_change: "set (pools ?t) = set (append (remove1 po (pools s)) [fst ?re])"
      unfolding k_mem_pool_free_def
      apply(case_tac "snd (snd (pool_free po num 0 (idset s))) = True")
       apply(case_tac "{t. (waitq s) t = Some (name po)} \<noteq> {}")
        apply(simp add:Let_def)
       apply(simp add:Let_def)
      using inv_block_k_mem_pool_free_helper[of po num s]
      pool_free_lm[where po = "po" and num = "num" and n = 0 and ids = "idset s" and re="pool_free po num 0 (idset s)"]
      set_helper[of po "pools s"]
      snd_conv fst_conv a0 by simp
    have "\<forall>p \<in> set (pools ?t). id_ids_valid p (idset ?t) \<and> diff_ids_valid p"
    proof-
      {fix pl
        assume a1: "pl \<in> set (pools ?t)"
        have ass1: "pl = fst ?re \<longrightarrow> id_ids_valid pl (idset ?t) \<and> diff_ids_valid pl"
          using p2 idset_change by auto
        have pl_belong: "pl \<noteq> fst ?re \<longrightarrow> pl \<in> set (pools s)"
          using pool_change a1
          using notin_set_remove1 by fastforce
        have ass2: "pl \<noteq> fst ?re \<longrightarrow> id_ids_valid pl (idset ?t) \<and> diff_ids_valid pl"
          using p0 pl_belong id_ids_ext2 idset_change s_in_re by blast
        have ?thesis using a1 ass1 ass2
          by (metis id_ids_ext2 idset_change notin_set_remove1 p0 p2 pool_change rotate1.simps(2) s_in_re set_ConsD set_rotate1)
      }
      then show ?thesis by auto
    qed
    then have ?thesis unfolding inv_ids_def by auto
  }
  moreover
  {assume c1: "snd (snd (pool_free po num 0 (idset s))) = False"
    have idset_nochange: "?t = s"
      unfolding k_mem_pool_free_def Let_def
      using c1 by auto
    then have "\<forall>p \<in> set (pools ?t). id_ids_valid p (idset ?t) \<and> diff_ids_valid p"
      using p0 by auto
    then have ?thesis unfolding inv_ids_def by auto
  }
  ultimately have ?thesis by blast
  then show ?thesis by auto
qed
(*
inductive block_in_list:: "Block \<Rightarrow> nat \<Rightarrow> Level_Freeset \<Rightarrow> bool"
  where b1: "(fst a = lv) \<and> ((fst (snd a) = FREE) \<longrightarrow> (snd (snd a)) \<in> (li ! lv)) \<and> ((fst (snd a) = ALLOC) \<longrightarrow> (snd (snd a)) \<notin> (li ! lv))
            \<Longrightarrow> block_in_list (Leaf a) lv li" |
        b2: "block_in_list ll (Suc lv) li \<and> block_in_list lr (Suc lv) li \<and> block_in_list rl (Suc lv) li \<and> block_in_list rr (Suc lv) li
            \<Longrightarrow> block_in_list (Node ll lr rl rr) lv li"

inductive_cases block_in_list_leaf_node:
  "block_in_list (Leaf a) lv li"
  "block_in_list (Node ll lr rl rr) lv li"

definition "block_in_list_valid p \<equiv> (\<forall>b\<in>set (zerolevelblocklist p). block_in_list b 0 (freelist p))"

definition "inv_block_in_list \<equiv> {s::State. (\<forall>p \<in> set (pools s). block_in_list_valid p)}"
  
lemma inv_block_in_list_s0: "s0 \<in> inv_block_in_list"
  unfolding s0_def inv_block_in_list_def block_in_list_valid_def using s0_def poolsinit by auto

lemma inv_block_in_list_time_tick: "s \<in> inv_block_in_list \<Longrightarrow> time_tick s \<in> inv_block_in_list"
  unfolding time_tick_def Let_def inv_block_in_list_def block_in_list_valid_def by auto
         
lemma inv_block_in_list_schedule: "s \<in> inv_block_in_list \<Longrightarrow> schedule s \<in> inv_block_in_list"
  unfolding schedule_def Let_def inv_block_in_list_def block_in_list_valid_def
  by (simp add: option.case_eq_if) 

lemma all_leaf_list_tree:
  "\<forall>a \<in> set bli. get_leaf a \<and> get_blocklevel a = 0 \<and> get_blocktype a = FREE \<and> get_blockid a \<in> idl \<Longrightarrow>
   \<forall>b \<in> set (fst (pool_init bli idl ids num)). get_leaf b \<and> get_blocklevel b = 0 \<and> get_blocktype b = FREE \<and>
        get_blockid b \<in> fst (snd (pool_init bli idl ids num))"
proof(induct "num" arbitrary: bli idl ids)
  case 0
  thus ?case by auto
next
  case (Suc n)
  obtain p where "pool_init bli idl ids (Suc n) = pool_init (bli@[Leaf(0, FREE, p)]) (idl\<union>{p}) (ids\<union>{p}) n"
    using pool_init_n[of "bli" "idl" ids n] by auto
  also have "\<forall>a \<in> set (bli@[Leaf(0, FREE, p)]). get_leaf a \<and> get_blocklevel a = 0 \<and> get_blocktype a = FREE \<and> (get_blockid a) \<in> idl\<union>{p}"
    using Suc(2) get_blocklevel_def get_blocktype_def get_blockid_def by auto
  ultimately show ?case using Suc.hyps by presburger
qed

lemma all_leaf_empty_list_tree: 
  "\<forall>b \<in> set (fst (pool_init [] {} ids num)). get_leaf b \<and> get_blocklevel b = 0 \<and> get_blocktype b = FREE \<and>
        get_blockid b \<in> fst (snd (pool_init [] {} ids num))"
proof-
  have "\<forall>a \<in> set []. get_leaf a \<and> get_blocklevel a = 0 \<and> get_blocktype a = FREE \<and> get_blockid a \<in> {}" by auto
  thus ?thesis using all_leaf_list_tree[of "[]" "{}" ids num]
    using all_leaf_list_tree by blast 
qed

lemma all_leaf_freelist_tree:
  "nlv > 0 \<Longrightarrow> (create_freelist nlv idl)!0 = idl"
proof(induct nlv)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  {assume a0: "Suc xa = 1"
    have xa_eq_0: "xa = 0" using a0 by auto
    have step0: "create_freelist (Suc xa) idl = [idl] @ [{}]" using xa_eq_0 by auto
    then have ?case by auto
  }
  moreover
  {assume a1: "Suc xa > 1"
    have xa_gr_0: "xa > 0" using a1 by auto
    have xa_hold: "create_freelist xa idl ! 0 = idl" using Suc(1) xa_gr_0 by auto
    have step1: "create_freelist (Suc xa) idl = create_freelist xa idl @ [{}]" by auto
    then have ?case using xa_hold create_freelist.simps
      by (metis append_is_Nil_conv butlast_snoc length_greater_0_conv list.simps(3) nth_butlast) 
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma inv_block_in_list_k_mem_pool_define: "s \<in> inv_block_in_list \<and> nlv > 0 \<Longrightarrow> fst (K_MEM_POOL_DEFINE s nam nlv num) \<in> inv_block_in_list"
proof -
  assume a0: "s \<in> inv_block_in_list \<and> nlv > 0"
  hence p0: "\<forall>p. p \<in> set (pools s) \<longrightarrow> (\<forall>b\<in>set (zerolevelblocklist p). block_in_list b 0 (freelist p))"
    unfolding inv_block_in_list_def block_in_list_valid_def by auto
  let ?t = "fst (K_MEM_POOL_DEFINE s nam nlv num)"
  { 
    have p1: "butlast (pools ?t) = pools s" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    have p2: "\<forall>p. p \<in> set (butlast (pools ?t)) \<longrightarrow> (\<forall>b\<in>set (zerolevelblocklist p). block_in_list b 0 (freelist p))"
      using p0 p1 by auto
    moreover
    have p3_0: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). get_leaf b \<and> get_blocklevel b = 0 \<and> get_blocktype b = FREE"
      unfolding K_MEM_POOL_DEFINE_def Let_def using all_leaf_empty_list_tree[where ids = "idset s" and num = "num"] by auto
    have p3_1: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). get_blockid b \<in> (freelist (last (pools ?t)))!0"
      unfolding K_MEM_POOL_DEFINE_def Let_def using all_leaf_freelist_tree a0
      proof -
        { fix tt :: "(nat \<times> block_state_type \<times> ID) tree"
          have ff1: "\<forall>s f. pools (idset_update f (s::State)) = pools s"
            by auto
          have "\<forall>s f. pools (pools_update f (s::State)) = f (pools s)"
            by simp
          moreover
          { assume "nlv - 1 = 0"
            moreover
            { assume "nlv - 1 = 0 \<and> tt \<in> set (fst (pool_init [] {} (idset s) num))"
              then have "nlv - 1 = 0 \<and> get_blockid tt \<in> fst (snd (pool_init [] {} (idset s) num))"
                by (metis (full_types) all_leaf_empty_list_tree)
              then have "get_blockid tt \<in> freelist (last (pools (s\<lparr>pools := pools s @ [\<lparr>zerolevelblocklist = fst (pool_init [] {} (idset s) num), freelist = create_freelist (nlv - 1) (fst (snd (pool_init [] {} (idset s) num))), n_levels = nlv, nmax = num, name = nam\<rparr>], idset := snd (snd (pool_init [] {} (idset s) num))\<rparr>))) ! 0"
                by force
            }
          ultimately have "tt \<in> set (fst (pool_init [] {} (idset s) num)) \<longrightarrow> get_blockid tt \<in> freelist (last (pools (s\<lparr>pools := pools s @ [\<lparr>zerolevelblocklist = fst (pool_init [] {} (idset s) num), freelist = create_freelist (nlv - 1) (fst (snd (pool_init [] {} (idset s) num))), n_levels = nlv, nmax = num, name = nam\<rparr>], idset := snd (snd (pool_init [] {} (idset s) num))\<rparr>))) ! 0"
            by meson
          }
        ultimately have "tt \<notin> set (zerolevelblocklist (last (pools (fst (s\<lparr>pools := pools s @ [\<lparr>zerolevelblocklist = fst (pool_init [] {} (idset s) num), freelist = create_freelist (nlv - 1) (fst (snd (pool_init [] {} (idset s) num))), n_levels = nlv, nmax = num, name = nam\<rparr>], idset := snd (snd (pool_init [] {} (idset s) num))\<rparr>, True))))) \<or> get_blockid tt \<in> freelist (last (pools (fst (s\<lparr>pools := pools s @ [\<lparr>zerolevelblocklist = fst (pool_init [] {} (idset s) num), freelist = create_freelist (nlv - 1) (fst (snd (pool_init [] {} (idset s) num))), n_levels = nlv, nmax = num, name = nam\<rparr>], idset := snd (snd (pool_init [] {} (idset s) num))\<rparr>, True)))) ! 0"
          using ff1 by (metis (no_types) Pool.select_convs(1) Pool.select_convs(2) all_leaf_empty_list_tree all_leaf_freelist_tree fst_conv last_snoc neq0_conv)
        }
        then show "\<forall>t\<in>set (zerolevelblocklist (last (pools (fst (s\<lparr>pools := pools s @ [\<lparr>zerolevelblocklist = fst (pool_init [] {} (idset s) num), freelist = create_freelist (nlv - 1) (fst (snd (pool_init [] {} (idset s) num))), n_levels = nlv, nmax = num, name = nam\<rparr>], idset := snd (snd (pool_init [] {} (idset s) num))\<rparr>, True))))). get_blockid t \<in> freelist (last (pools (fst (s\<lparr>pools := pools s @ [\<lparr>zerolevelblocklist = fst (pool_init [] {} (idset s) num), freelist = create_freelist (nlv - 1) (fst (snd (pool_init [] {} (idset s) num))), n_levels = nlv, nmax = num, name = nam\<rparr>], idset := snd (snd (pool_init [] {} (idset s) num))\<rparr>, True)))) ! 0"
          by blast
      qed
    have p3: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). get_leaf b \<and> get_blocklevel b = 0 \<and> get_blocktype b = FREE \<and>
              get_blockid b \<in> (freelist (last (pools ?t)))!0"
      using p3_0 p3_1 by auto
    have p4: "\<forall>b \<in> set (zerolevelblocklist (last (pools ?t))). block_in_list b 0 (freelist (last (pools ?t)))"
      using p3 block_in_list_leaf_node(1) get_leaf_def get_blocklevel_def get_blocktype_def get_blockid_def
      proof -
        { fix tt :: "(nat \<times> block_state_type \<times> nat) tree"
          obtain pp :: "(nat \<times> block_state_type \<times> nat) tree \<Rightarrow> nat \<times> block_state_type \<times> nat" where
            ff1: "\<forall>t. Leaf (pp t) = t \<or> \<not> get_leaf t"
            by (metis (no_types) get_leaf.simps(2) idsets_block.cases)
          have ff2: "\<forall>p. fst (snd p) = FREE \<or> Leaf p \<notin> set (zerolevelblocklist (last (pools (fst (K_MEM_POOL_DEFINE s nam nlv num)))))"
            using get_blocktype_def p3 by fastforce
          have ff3: "\<forall>f fa t. (case t of Leaf x \<Rightarrow> fa x::nat | Node x xa xb xc \<Rightarrow> f x xa xb xc) = fa (pp t) \<or> \<not> get_leaf t"
            using ff1 by (metis tree.simps(5))
          have "\<forall>p. snd (snd p) \<in> freelist (last (pools (fst (K_MEM_POOL_DEFINE s nam nlv num)))) ! 0 \<or> Leaf p \<notin> set (zerolevelblocklist (last (pools (fst (K_MEM_POOL_DEFINE s nam nlv num)))))"
            using get_blockid_def p3 by fastforce
          then have "tt \<notin> set (zerolevelblocklist (last (pools (fst (K_MEM_POOL_DEFINE s nam nlv num))))) \<or> block_in_list tt 0 (freelist (last (pools (fst (K_MEM_POOL_DEFINE s nam nlv num)))))"
            using ff3 ff2 ff1 by (metis (no_types) b1 block_state_type.distinct(1) get_blocklevel_def p3) }
        then show ?thesis
          by blast
      qed
    moreover
    have p5: "pools ?t = append (butlast (pools ?t)) [(last (pools ?t))]" unfolding K_MEM_POOL_DEFINE_def Let_def by auto
    with p2 p4 have "\<forall>p. p \<in> set (pools ?t) \<longrightarrow> (\<forall>b\<in>set ((zerolevelblocklist p)). block_in_list b 0 (freelist p))"
      by (smt butlast.simps(2) butlast_append in_set_butlastD in_set_conv_decomp_last last.simps last_appendR list.distinct(1))
  }
  then show ?thesis unfolding inv_block_in_list_def
    by (simp add: block_in_list_valid_def)
qed

lemma block_in_list_alloc_leaf_case1:
  "lv < length li \<Longrightarrow>
  lv < curl \<Longrightarrow>
  block_in_list (Leaf x) curl li \<Longrightarrow>
  block_in_list (fst (alloc (Leaf x) li lv ids curl)) curl (fst (snd (alloc (Leaf x) li lv ids curl)))"
  by auto

lemma block_in_list_alloc_leaf_case2:
  "lv < length li \<Longrightarrow>
  \<not> lv < curl \<Longrightarrow>
  lv = curl \<Longrightarrow>
  block_in_list (Leaf x) curl li \<Longrightarrow>
  block_in_list (fst (alloc (Leaf x) li lv ids curl)) curl (fst (snd (alloc (Leaf x) li lv ids curl)))"
proof-
  assume a0: "lv < length li"
     and a1: "\<not> lv < curl"
     and a2: "lv = curl"
     and a3: "block_in_list (Leaf x) curl li"
  {assume leaf_alloc: "fst (snd x) = ALLOC"
    then have ?thesis using a1 a2 a3 by auto
  }
  moreover
  {assume leaf_free: "fst (snd x) = FREE"
    have free_hold1: "fst x = curl"
      using a3 leaf_free block_in_list_leaf_node(1) by blast
    have free_hold2: "snd (snd x) \<in> li ! curl"
      using a3 leaf_free block_in_list_leaf_node(1) by blast
    have len: "curl < length li"
      using a0 a2 by auto
    have type_change: "fst (alloc (Leaf x) li lv ids curl) = Leaf (fst x, ALLOC, snd (snd x))"
      using a1 a2 alloc.simps(1) leaf_free by auto
    have list_change: "fst (snd (alloc (Leaf x) li lv ids curl)) = li[curl := li ! curl - {snd (snd x)}]"
      using a1 a2 alloc.simps(1) leaf_free by auto
    have no_belong: "snd (snd x) \<notin> (li[curl := li ! curl - {snd (snd x)}]) ! curl"
      using free_hold2 len by auto
    have ?thesis using free_hold1 type_change list_change no_belong block_in_list_leaf_node(1) b1 by simp
  }
  ultimately have ?thesis
    using block_state_type.exhaust by blast 
  then show ?thesis by auto
qed
 
lemma block_in_list_alloc_leaf_case3:
  "lv < length li \<Longrightarrow>
  \<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) = ALLOC \<Longrightarrow>
  block_in_list (Leaf x) curl li \<Longrightarrow>
  block_in_list (fst (alloc (Leaf x) li lv ids curl)) curl (fst (snd (alloc (Leaf x) li lv ids curl)))"
  by auto

lemma inv_block_in_list_divide:
  "Suc (fst v) < length li \<Longrightarrow>
  fst (divide (Leaf v) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  snd (snd ll) \<in> (fst (snd (divide (Leaf v) li ids))) ! (Suc (fst v)) \<and>
  snd (snd lr) \<in> (fst (snd (divide (Leaf v) li ids))) ! (Suc (fst v)) \<and>
  snd (snd rl) \<in> (fst (snd (divide (Leaf v) li ids))) ! (Suc (fst v)) \<and>
  snd (snd rr) \<in> (fst (snd (divide (Leaf v) li ids))) ! (Suc (fst v))"
  unfolding divide_def Let_def by auto

lemma inv_block_in_list_divide_nobelong:
  "fst v < length li \<Longrightarrow>
  (fst (snd (divide (Leaf v) li ids))) ! (fst v) = li ! (fst v) - {snd (snd v)}"
  unfolding divide_def Let_def by auto

lemma inv_block_in_list_divide_belong:
  "Suc (fst v) < length li \<Longrightarrow>
  fst (divide (Leaf v) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  (fst (snd (divide (Leaf v) li ids))) ! (Suc (fst v)) = li ! (Suc (fst v)) \<union> {snd (snd ll), snd (snd lr), snd (snd rl), snd (snd rr)}"
  unfolding divide_def Let_def by auto

lemma inv_block_in_list_divide_list:
  "Suc (fst x) < length li \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  \<forall>l. l < length li \<and> l \<noteq> fst x \<and> l \<noteq> Suc (fst x) \<longrightarrow> (fst (snd (divide (Leaf x) li ids))) ! l = li ! l"
  unfolding divide_def Let_def by auto

lemma inv_block_in_list_alloc_leaf_f1:
  "\<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newli = fst (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  newids = snd (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))"
proof-
  assume a0: "\<not> lv < curl"
     and a1: "lv \<noteq> curl"
     and a2: "fst (snd x) \<noteq> ALLOC"
     and a3: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
     and a4: "newli = fst (snd (divide (Leaf x) li ids))"
     and a5: "newids = snd (snd (divide (Leaf x) li ids))"
  let ?p = "let re = divide (Leaf x) li ids;
                node = fst re;
                freeset = fst (snd re);
                newids = snd (snd re) in
            case node of (Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)) \<Rightarrow>
              let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
              (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True) |
                         _ \<Rightarrow> (Leaf x, li, ids, False)"
  have p0: "fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd ?p)" using a0 a1 a2 by auto
  let ?b = "let re = divide (Leaf x) li ids;
                node = fst re;
                freeset = fst (snd re);
                newids = snd (snd re) in
            (let c1 = alloc (Leaf ll) freeset lv newids (Suc curl) in
              (Node (fst c1) (Leaf lr) (Leaf rl) (Leaf rr), fst (snd c1), fst (snd (snd c1)), True))"
  have p1: "?p = ?b" unfolding Let_def using a3 by auto
  let ?newli = "fst (snd (divide (Leaf x) li ids))"
  let ?newids = "snd (snd (divide (Leaf x) li ids))"
  have p2: "fst (snd ?b) = fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))"
    unfolding Let_def by auto
  have p3: "fst (snd ?p) = fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))"
    using p1 p2 by auto
  have p4: "fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))"
    using p0 p3 by auto
  then show ?thesis using a4 a5 by auto
qed

lemma inv_block_in_list_alloc_leaf_f2:
  "fst x = curl \<Longrightarrow>
  finite ids \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newli = fst (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  newids = snd (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  \<not> lv < Suc curl \<Longrightarrow>
  lv = Suc curl \<Longrightarrow>
  lv < length li \<Longrightarrow>
  snd (snd lr) \<in> (fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) ! (Suc curl) \<and>
  snd (snd rl) \<in> (fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) ! (Suc curl) \<and>
  snd (snd rr) \<in> (fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) ! (Suc curl)"
proof-
  assume a0: "fst x = curl"
     and a1: "finite ids"
     and a2: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
     and a3: "\<not> lv < Suc curl"
     and a4: "lv = Suc curl"
     and a5: "lv < length li"
     and a6: "newli = fst (snd (divide (Leaf x) li ids))"
     and a7: "newids = snd (snd (divide (Leaf x) li ids))"
  have ll_free: "fst (snd ll) = FREE"
    using a2 divide_def Let_def
    by (smt prod.collapse prod.inject tree.inject(1) tree.inject(2) tree.simps(5))
  have lr_noeq_ll: "snd (snd lr) \<noteq> snd (snd ll)"
    using a1 a2 a3 divide_diff by metis 
  have rl_noeq_ll: "snd (snd rl) \<noteq> snd (snd ll)"
    using a1 a2 a3 divide_diff by metis 
  have rr_noeq_ll: "snd (snd rr) \<noteq> snd (snd ll)"
    using a1 a2 a3 divide_diff by metis
  have len1: "Suc (fst x) < length li"
    using a0 a4 a5 by auto
  have node_belong: "snd (snd ll) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) \<and>
                     snd (snd lr) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) \<and>
                     snd (snd rl) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) \<and>
                     snd (snd rr) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl)"
    using inv_block_in_list_divide len1 a0 a2 by blast 
  let ?newli = "fst (snd (divide (Leaf x) li ids))"
  let ?newids = "snd (snd (divide (Leaf x) li ids))"
  have list_change: "fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl))) = ?newli[(Suc curl) := ?newli ! (Suc curl) - {snd (snd ll)}]"
    using alloc.simps(1) a4 a5 ll_free by auto
  have len_nochange: "length li = length (fst (snd (divide (Leaf x) li ids)))"
    unfolding divide_def Let_def by auto
  have len2: "Suc curl < length (fst (snd (divide (Leaf x) li ids)))"
    using len_nochange a4 a5 by auto
  have lr_belong: "snd (snd lr) \<in> (?newli[(Suc curl) := ?newli ! (Suc curl) - {snd (snd ll)}]) ! (Suc curl)"
    using node_belong len2 lr_noeq_ll by auto
  have rl_belong: "snd (snd rl) \<in> (?newli[(Suc curl) := ?newli ! (Suc curl) - {snd (snd ll)}]) ! (Suc curl)"
    using node_belong len2 rl_noeq_ll by auto
  have rr_belong: "snd (snd rr) \<in> (?newli[(Suc curl) := ?newli ! (Suc curl) - {snd (snd ll)}]) ! (Suc curl)"
    using node_belong len2 rr_noeq_ll by auto
  show ?thesis using lr_belong rl_belong rr_belong list_change a6 a7 by auto
qed

lemma inv_block_in_list_alloc_leaf_f3_h:
  "fst x = curl \<Longrightarrow>
  lv < length li \<Longrightarrow>
  \<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  \<forall>l. l < length li \<and> l \<le> fst x \<longrightarrow> (fst (snd (alloc (Leaf x) li lv ids curl))) ! l = (fst (snd (divide (Leaf x) li ids))) ! l"
proof(induct "lv - curl" arbitrary: curl x li ids)
  case 0
  then show ?case by linarith
next
  case (Suc xa)
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and ll_free: "fst (snd ll) = FREE"
      and ll_level: "fst ll = Suc curl"
    unfolding divide_def Let_def using Suc(3) by auto
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto
    let ?newli = "fst (snd (divide (Leaf x) li ids))"
    let ?newids = "snd (snd (divide (Leaf x) li ids))"
    have len_nochange: "length li = length ?newli"
      unfolding divide_def Let_def by auto
    have freeset_change: "fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))"
      using inv_block_in_list_alloc_leaf_f1 Suc(5,6,7) pdivide by auto
    have list_alloc: "fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl))) = ?newli[(Suc curl) := ?newli ! (Suc curl) - {snd (snd ll)}]"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl ll_free by auto
    have list_eq: "\<forall>l. l < length ?newli \<and> l \<le> curl \<longrightarrow> (fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))) ! l = ?newli ! l"
      using list_alloc by simp
    have ?case using freeset_change list_eq Suc(3) len_nochange by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(5,6) by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    let ?newli = "fst (snd (divide (Leaf x) li ids))"
    let ?newids = "snd (snd (divide (Leaf x) li ids))"
    have len_nachange: "length li = length ?newli"
      unfolding divide_def Let_def by auto
    have lv_less: "lv < length ?newli"
      using len_nachange Suc(4) by auto
    have step1: "\<forall>l. l < length ?newli \<and> l \<le> fst ll \<longrightarrow> fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl))) ! l = fst (snd (divide (Leaf ll) ?newli ?newids)) ! l"
      using Suc(1) xa_lv_suc_curl ll_level lv_less de_lv_less_suc_curl de_lv_suc_curl ll_free by auto
    have freeset_change: "fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))"
      using inv_block_in_list_alloc_leaf_f1 Suc(5,6,7) pdivide by auto
    have step2: "\<forall>l. l < length li \<and> l \<le> fst ll \<longrightarrow> fst (snd (alloc (Leaf x) li lv ids curl)) ! l = fst (snd (divide (Leaf ll) ?newli ?newids)) ! l"
      using step1 freeset_change len_nachange by auto
    obtain b1 b2 b3 b4
      where ll_divide: "fst (divide (Leaf ll) ?newli ?newids) = Node (Leaf b1) (Leaf b2) (Leaf b3) (Leaf b4)"
      unfolding divide_def Let_def by auto
    have suc_fst_ll: "Suc (fst ll) < length ?newli"
      using Suc.prems(2) de_lv_less_suc_curl de_lv_suc_curl len_nachange ll_level by linarith
    have step3: "\<forall>l. l < length li \<and> l < fst ll \<longrightarrow> fst (snd (divide (Leaf ll) ?newli ?newids)) ! l = ?newli ! l"
      using inv_block_in_list_divide_list suc_fst_ll ll_divide len_nachange by auto
    have x_less_ll: "fst x < fst ll"
      using ll_level Suc(3) by auto
    have step: "\<forall>l. l < length li \<and> l \<le> fst x \<longrightarrow> fst (snd (alloc (Leaf x) li lv ids curl)) ! l = ?newli ! l"
      using step2 step3 x_less_ll by auto
    then have ?case by auto
  }
  ultimately have ?case by (metis One_nat_def Suc_lessI zero_less_Suc) 
  then show ?case by auto
qed

lemma inv_block_in_list_alloc_leaf_f3:
  "fst x = curl \<Longrightarrow>
  finite ids \<Longrightarrow>
  fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr) \<Longrightarrow>
  newli = fst (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  newids = snd (snd (divide (Leaf x) li ids)) \<Longrightarrow>
  \<not> lv < Suc curl \<Longrightarrow>
  lv \<noteq> Suc curl \<Longrightarrow>
  lv < length li \<Longrightarrow>
  snd (snd lr) \<in> (fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) ! (Suc curl) \<and>
  snd (snd rl) \<in> (fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) ! (Suc curl) \<and>
  snd (snd rr) \<in> (fst (snd (alloc (Leaf ll) newli lv newids (Suc curl)))) ! (Suc curl)"
proof-
  assume a0: "fst x = curl"
     and a1: "finite ids"
     and a2: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
     and a3: "\<not> lv < Suc curl"
     and a4: "lv \<noteq> Suc curl"
     and a5: "lv < length li"
     and a6: "newli = fst (snd (divide (Leaf x) li ids))"
     and a7: "newids = snd (snd (divide (Leaf x) li ids))"
  have ll_free: "fst (snd ll) = FREE"
    using a2 divide_def Let_def
    by (smt prod.collapse prod.inject tree.inject(1) tree.inject(2) tree.simps(5))
  have ll_level: "fst ll = Suc (fst x)"
    using a2 divide_def Let_def
    by (smt prod.collapse prod.inject tree.inject(1) tree.inject(2) tree.simps(5))
  have lr_noeq_ll: "snd (snd lr) \<noteq> snd (snd ll)"
    using a1 a2 a3 divide_diff by metis 
  have rl_noeq_ll: "snd (snd rl) \<noteq> snd (snd ll)"
    using a1 a2 a3 divide_diff by metis 
  have rr_noeq_ll: "snd (snd rr) \<noteq> snd (snd ll)"
    using a1 a2 a3 divide_diff by metis
  have len1: "Suc (fst x) < length li"
    using a0 a3 a4 a5 by auto
  have node_belong: "snd (snd ll) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) \<and>
                     snd (snd lr) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) \<and>
                     snd (snd rl) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) \<and>
                     snd (snd rr) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl)"
    using inv_block_in_list_divide len1 a0 a2 by blast
  let ?newli = "fst (snd (divide (Leaf x) li ids))"
  let ?newids = "snd (snd (divide (Leaf x) li ids))"
  have len_nochange: "length li = length (fst (snd (divide (Leaf x) li ids)))"
    unfolding divide_def Let_def by auto
  have len2: "Suc curl < length (fst (snd (divide (Leaf x) li ids)))"
    using len_nochange a3 a4 a5 by auto
  have len3: "fst ll < length (fst (snd (divide (Leaf x) li ids)))"
    using ll_level len1 len_nochange by auto
  have len4: "lv < length (fst (snd (divide (Leaf x) li ids)))"
    using a5 len_nochange by auto
  have list_change: "(fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))) ! (Suc curl) =
                     (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) - {snd (snd ll)}"
  proof-
    have ll_nobelong: "(fst (snd (divide (Leaf ll) ?newli ?newids))) ! (Suc curl) = ?newli ! (Suc curl) - {snd (snd ll)}"
      using inv_block_in_list_divide_nobelong len3 ll_level a0 by metis
    have "(fst (snd (alloc (Leaf ll) ?newli lv ?newids (Suc curl)))) ! (Suc curl) = (fst (snd (divide (Leaf ll) ?newli ?newids))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f3_h ll_level a0 len4 a3 a4 ll_free len2 by auto
    then show ?thesis using ll_nobelong by auto
  qed
  have lr_belong: "snd (snd lr) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) - {snd (snd ll)}"
    using node_belong len2 lr_noeq_ll by auto
  have rl_belong: "snd (snd rl) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) - {snd (snd ll)}"
    using node_belong len2 rl_noeq_ll by auto
  have rr_belong: "snd (snd rr) \<in> (fst (snd (divide (Leaf x) li ids))) ! (Suc curl) - {snd (snd ll)}"
    using node_belong len2 rr_noeq_ll by auto
  show ?thesis using lr_belong rl_belong rr_belong list_change a6 a7 by auto
qed

lemma inv_block_in_list_finite_ids:
  "finite ids \<Longrightarrow>
  finite (snd (snd (divide (Leaf x) li ids)))"
proof-
  assume a0: "finite ids"
  have p0: "snd (snd (divide (Leaf x) li ids)) = snd (snd (snd (snd (getnewid ids))))"
    unfolding divide_def Let_def by auto
  obtain xa xb xc xd
    where obtain_divide: "snd (snd (divide (Leaf x) li ids)) = ids \<union> {xa, xb, xc, xd}"
    using p0 exists_p_getnewid by (metis sndI)
  have "finite (ids \<union> {xa, xb, xc, xd})" using a0 by auto
  then show ?thesis using obtain_divide by auto
qed

lemma block_in_list_alloc_leaf_case4:
  "lv < length li \<Longrightarrow>
  \<not> lv < curl \<Longrightarrow>
  lv \<noteq> curl \<Longrightarrow>
  fst (snd x) \<noteq> ALLOC \<Longrightarrow>
  finite ids \<Longrightarrow>
  block_in_list (Leaf x) curl li \<Longrightarrow>
  block_in_list (fst (alloc (Leaf x) li lv ids curl)) curl (fst (snd (alloc (Leaf x) li lv ids curl)))"
proof(induct "lv - curl" arbitrary: curl x li ids)
  case 0
  then show ?case by linarith
next
  case (Suc xa)
  have leaf_hold1: "fst x = curl"
    using Suc(8) block_in_list_leaf_node(1) by blast
  have leaf_hold2: "fst (snd x) = FREE"
    using Suc(6) block_state_type.exhaust by blast 
  obtain ll lr rl rr
    where pdivide: "fst (divide (Leaf x) li ids) = Node (Leaf ll) (Leaf lr) (Leaf rl) (Leaf rr)"
      and ll_level: "fst ll = Suc curl"
      and lr_level: "fst lr = Suc curl"
      and rl_level: "fst rl = Suc curl"
      and rr_level: "fst rr = Suc curl"
      and pll_alloc: "fst (snd ll) \<noteq> ALLOC" and pll_free: "fst (snd ll) = FREE"
      and plr_alloc: "fst (snd lr) \<noteq> ALLOC" and plr_free: "fst (snd lr) = FREE"
      and prl_alloc: "fst (snd rl) \<noteq> ALLOC" and prl_free: "fst (snd rl) = FREE"
      and prr_alloc: "fst (snd rr) \<noteq> ALLOC" and prr_free: "fst (snd rr) = FREE"
    unfolding divide_def Let_def using leaf_hold1 by auto
  have len1: "Suc (fst x) < length li"
    using Suc(3,4,5) leaf_hold1 by auto
  have ll_id: "snd (snd ll) \<in> fst (snd (divide (Leaf x) li ids)) ! (Suc curl)"
    using inv_block_in_list_divide len1 pdivide leaf_hold1 by blast
  have lr_id: "snd (snd lr) \<in> fst (snd (divide (Leaf x) li ids)) ! (Suc curl)"
    using inv_block_in_list_divide len1 pdivide leaf_hold1 by blast
  have rl_id: "snd (snd rl) \<in> fst (snd (divide (Leaf x) li ids)) ! (Suc curl)"
    using inv_block_in_list_divide len1 pdivide leaf_hold1 by blast
  have rr_id: "snd (snd rr) \<in> fst (snd (divide (Leaf x) li ids)) ! (Suc curl)"
    using inv_block_in_list_divide len1 pdivide leaf_hold1 by blast
  let ?li = "fst (snd (divide (Leaf x) li ids))"
  let ?ids = "snd (snd (divide (Leaf x) li ids))"
  have block_in_list_ll: "block_in_list (Leaf ll) (Suc curl) ?li"
    using ll_level pll_alloc pll_free ll_id by (simp add: b1)
  have block_in_list_lr: "block_in_list (Leaf lr) (Suc curl) ?li"
    using lr_level plr_alloc plr_free lr_id by (simp add: b1)
  have block_in_list_rl: "block_in_list (Leaf rl) (Suc curl) ?li"
    using rl_level prl_alloc prl_free rl_id by (simp add: b1)
  have block_in_list_rr: "block_in_list (Leaf rr) (Suc curl) ?li"
    using rr_level prr_alloc prr_free rr_id by (simp add: b1)
  have len_nochange: "length li = length (fst (snd (divide (Leaf x) li ids)))"
    unfolding divide_def Let_def by auto
  have len2: "lv < length (fst (snd (divide (Leaf x) li ids)))"
    using Suc(3) len_nochange by auto
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_less_curl: "\<not> lv < curl" using lv_suc_curl by auto
    have de_lv_eq_curl: "\<not> lv = curl" using lv_suc_curl by auto
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto
    have step1: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h de_lv_less_curl de_lv_eq_curl Suc(6) pdivide by auto
    have ll_alloc: "fst (alloc (Leaf ll) ?li lv ?ids (Suc curl)) = Leaf (fst ll, ALLOC, snd (snd ll))"
      using alloc.simps(1) de_lv_less_suc_curl lv_suc_curl pll_free by auto
    have block_in_list_ll_alloc: "block_in_list (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using block_in_list_alloc_leaf_case2 len2 de_lv_less_suc_curl lv_suc_curl block_in_list_ll by (simp add: b1)
    have freeset_change: "fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))"
      using inv_block_in_list_alloc_leaf_f1 de_lv_less_curl de_lv_eq_curl Suc(6) pdivide by auto

    have lr_id_belong: "snd (snd lr) \<in> (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f2 leaf_hold1 Suc(7) pdivide Suc(3) de_lv_less_suc_curl lv_suc_curl by auto
    have block_in_list_lr_change: "block_in_list (Leaf lr) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using lr_level plr_alloc plr_free lr_id_belong by (simp add: b1)

    have rl_id_belong: "snd (snd rl) \<in> (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f2 leaf_hold1 Suc(7) pdivide Suc(3) de_lv_less_suc_curl lv_suc_curl by auto
    have block_in_list_rl_change: "block_in_list (Leaf rl) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using rl_level prl_alloc prl_free rl_id_belong by (simp add: b1)

    have rr_id_belong: "snd (snd rr) \<in> (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f2 leaf_hold1 Suc(7) pdivide Suc(3) de_lv_less_suc_curl lv_suc_curl by auto
    have block_in_list_rr_change: "block_in_list (Leaf rr) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using rr_level prr_alloc prr_free rr_id_belong by (simp add: b1)

    have block_in_list_x_alloc: "block_in_list (fst (alloc (Leaf x) li lv ids curl)) curl (fst (snd (alloc (Leaf x) li lv ids curl)))"
      using step1 block_in_list_ll_alloc block_in_list_lr_change block_in_list_rl_change block_in_list_rr_change freeset_change by (simp add:b2)
    then have ?case by auto
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_less_suc_curl: "\<not> lv < Suc curl" using Suc(4,5) by auto
    have de_lv_le_curl: "\<not> lv < curl" using de_lv_less_suc_curl by auto
    have de_lv_suc_curl: "lv \<noteq> Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_equal_curl: "lv \<noteq> curl" using de_lv_less_suc_curl de_lv_suc_curl by auto
    have step2: "fst (alloc (Leaf x) li lv ids curl) = Node (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Leaf lr) (Leaf rl) (Leaf rr)"
      using inv_alloc_leaf_h Suc(4,5,6) pdivide by auto
    have block_in_list_ll_alloc2: "block_in_list (fst (alloc (Leaf ll) ?li lv ?ids (Suc curl))) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using Suc(1) xa_lv_suc_curl len2 de_lv_less_suc_curl de_lv_suc_curl pll_alloc Suc(7) block_in_list_ll by (simp add: inv_block_in_list_finite_ids)
    have freeset_change2: "fst (snd (alloc (Leaf x) li lv ids curl)) = fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))"
      using inv_block_in_list_alloc_leaf_f1 de_lv_le_curl de_lv_equal_curl Suc(6) pdivide by auto

    have lr_id_belong2: "snd (snd lr) \<in> (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f3 leaf_hold1 Suc(7) pdivide de_lv_less_suc_curl de_lv_suc_curl Suc(3) by auto
    have block_in_list_lr_change2: "block_in_list (Leaf lr) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using lr_level plr_alloc plr_free lr_id_belong2 by (simp add: b1)

    have rl_id_belong2: "snd (snd rl) \<in> (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f3 leaf_hold1 Suc(7) pdivide de_lv_less_suc_curl de_lv_suc_curl Suc(3) by auto
    have block_in_list_rl_change2: "block_in_list (Leaf rl) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using rl_level prl_alloc prl_free rl_id_belong2 by (simp add: b1)

    have rr_id_belong2: "snd (snd rr) \<in> (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl)))) ! (Suc curl)"
      using inv_block_in_list_alloc_leaf_f3 leaf_hold1 Suc(7) pdivide de_lv_less_suc_curl de_lv_suc_curl Suc(3) by auto
    have block_in_list_rr_change2: "block_in_list (Leaf rr) (Suc curl) (fst (snd (alloc (Leaf ll) ?li lv ?ids (Suc curl))))"
      using rr_level prr_alloc prr_free rr_id_belong2 by (simp add: b1)

    have block_in_list_x_alloc2: "block_in_list (fst (alloc (Leaf x) li lv ids curl)) curl (fst (snd (alloc (Leaf x) li lv ids curl)))"
      using step2 block_in_list_ll_alloc2 block_in_list_lr_change2 block_in_list_rl_change2 block_in_list_rr_change2 freeset_change2 by (simp add:b2)
    then have ?case by auto
  }
  ultimately have ?case by linarith
  then show ?case by auto
qed

lemma block_in_list_alloc_node_h:
  "lv < length li \<Longrightarrow>
  block_in_list b curl li \<Longrightarrow>
  lv = curl \<Longrightarrow>
  block_in_list (fst (alloc b li lv ids curl)) curl (fst (snd (alloc b li lv ids curl)))"
proof(induct b)
  case (Leaf x)
  then show ?case using block_in_list_alloc_leaf_case2 by auto
next
  case (Node b1 b2 b3 b4)
  have block_in_list_node: "block_in_list (Node b1 b2 b3 b4) curl li"
    by (simp add: Node.prems(2))
  assume a0: "lv = curl"
  have lv_le_suc_curl: "lv < Suc curl" using a0 by auto
  have "block_in_list (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) curl (fst (snd (alloc (Node b1 b2 b4 b4) li lv ids curl)))"
    using alloc.simps(2) lv_le_suc_curl block_in_list_node by auto
  then show ?case by (simp add: a0) 
qed

lemma block_in_list_alloc_node:
  "lv < length li \<Longrightarrow>
  block_in_list (Node b1 b2 b3 b4) curl li \<Longrightarrow>
  \<not> lv < Suc curl \<Longrightarrow>
  finite ids \<Longrightarrow>
  block_in_list (fst (alloc (Node b1 b2 b3 b4) li lv ids curl)) curl (fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)))"
proof(induct "lv - curl" arbitrary: curl b1 b2 b3 b4 li ids)
  case 0
  then show ?case by auto
next
  case (Suc xa)
  have block_in_list_b1: "block_in_list b1 (Suc curl) li"
    using Suc(4) block_in_list_leaf_node(2) by blast
  have block_in_list_b2: "block_in_list b2 (Suc curl) li"
    using Suc(4) block_in_list_leaf_node(2) by blast
  have block_in_list_b3: "block_in_list b3 (Suc curl) li"
    using Suc(4) block_in_list_leaf_node(2) by blast
  have block_in_list_b4: "block_in_list b4 (Suc curl) li"
    using Suc(4) block_in_list_leaf_node(2) by blast
  {assume xa_eq_1: "Suc xa = 1"
    have lv_suc_curl: "lv = Suc curl" using Suc(2) xa_eq_1 by linarith
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_suc_curl by auto

    {assume c1: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b1: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto
    have list_b1: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b1 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c1 by auto

    have block_in_list_alloc_b1: "block_in_list (fst (alloc b1 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
      using block_in_list_alloc_node_h Suc(3) block_in_list_b1 lv_suc_curl by auto
    have block_in_list_alloc_b1_b2: "block_in_list b2 (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b2 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])"
            using block_in_list_b2 sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b2 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b2 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b1_b3: "block_in_list b3 (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b3 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b3 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b3 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b1_b4: "block_in_list b4 (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b1 = True"
        obtain x where c11: "b1 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b4 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b4 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b1 = False"
        obtain m1 m2 m3 m4 where c21: "b1 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b4 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_node_b1: "block_in_list (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) curl (fst (snd (alloc b1 li lv ids (Suc curl))))"
      using block_in_list_alloc_b1 block_in_list_alloc_b1_b2 block_in_list_alloc_b1_b3 block_in_list_alloc_b1_b4 by (simp add: b2)
    have ?case using alloc_b1 list_b1 block_in_list_node_b1 by auto
    }
    moreover
    {assume c2: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b2: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto
    have list_b2: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b2 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c2 by auto

    have block_in_list_alloc_b2: "block_in_list (fst (alloc b2 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
      using block_in_list_alloc_node_h Suc(3) block_in_list_b2 lv_suc_curl by auto
    have block_in_list_alloc_b2_b1: "block_in_list b1 (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          then have a12: "block_in_list b1 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b1 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b1 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b2_b3: "block_in_list b3 (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b3 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b3 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b3 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b2_b4: "block_in_list b4 (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b2 = True"
        obtain x where c11: "b2 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b4 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b4 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b2 = False"
        obtain m1 m2 m3 m4 where c21: "b2 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b4 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_node_b2: "block_in_list (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) curl (fst (snd (alloc b2 li lv ids (Suc curl))))"
      using block_in_list_alloc_b2 block_in_list_alloc_b2_b1 block_in_list_alloc_b2_b3 block_in_list_alloc_b2_b4 by (simp add: b2)
    have ?case using alloc_b2 list_b2 block_in_list_node_b2 by auto
    }
    moreover
    {assume c3: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b3: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto
    have list_b3: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b3 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c3 by auto

    have block_in_list_alloc_b3: "block_in_list (fst (alloc b3 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
      using block_in_list_alloc_node_h Suc(3) block_in_list_b3 lv_suc_curl by auto
    have block_in_list_alloc_b3_b1: "block_in_list b1 (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          then have a12: "block_in_list b1 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b1 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b1 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b3_b2: "block_in_list b2 (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          then have a12: "block_in_list b2 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b2 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b2 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b3_b4: "block_in_list b4 (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b3 = True"
        obtain x where c11: "b3 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b4 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b4 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b3 = False"
        obtain m1 m2 m3 m4 where c21: "b3 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b4 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_node_b3: "block_in_list (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) curl (fst (snd (alloc b3 li lv ids (Suc curl))))"
      using block_in_list_alloc_b3 block_in_list_alloc_b3_b1 block_in_list_alloc_b3_b2 block_in_list_alloc_b3_b4 by (simp add: b2)
      have ?case using alloc_b3 list_b3 block_in_list_node_b3 by auto
    }
    moreover
    {assume c4: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b4: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto
    have list_b4: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c4 by auto

    have block_in_list_alloc_b4: "block_in_list (fst (alloc b4 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
      using block_in_list_alloc_node_h Suc(3) block_in_list_b4 lv_suc_curl by auto
    have block_in_list_alloc_b4_b1: "block_in_list b1 (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          then have a12: "block_in_list b1 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b1 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b1 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b4_b2: "block_in_list b2 (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          then have a12: "block_in_list b2 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b2 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b2 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_alloc_b4_b3: "block_in_list b3 (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
    proof-
      {assume c10: "get_leaf b4 = True"
        obtain x where c11: "b4 = Leaf x" using c10 by (metis get_leaf.simps(2) is_Leaf_def tree.collapse(2))
        {assume a10: "fst (snd x) = FREE"
          have a11: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}]"
            using alloc.simps(1) lv_suc_curl a10 by auto
          have a12: "block_in_list b3 (Suc curl) (li[(Suc curl) := li ! (Suc curl) - {snd (snd x)}])" sorry
          have ?thesis using c11 a11 a12 by auto
        }moreover
        {assume a20: "fst (snd x) = ALLOC"
          have a21: "fst (snd (alloc (Leaf x) li lv ids (Suc curl))) = li"
            using alloc.simps(1) lv_suc_curl a20 by auto
          have ?thesis using c11 block_in_list_b3 a21 by auto
        }
        ultimately have ?thesis using block_state_type.exhaust by blast
        then have ?thesis using c11 by simp
      }moreover
      {assume c20: "get_leaf b4 = False"
        obtain m1 m2 m3 m4 where c21: "b4 = Node m1 m2 m3 m4" using c20 by (metis get_leaf.simps(1) is_Leaf_def tree.collapse(2))
        have c22: "fst (snd (alloc (Node m1 m2 m3 m4) li lv ids (Suc curl))) = li"
          using alloc.simps(2) lv_suc_curl by auto
        have ?thesis using c21 block_in_list_b3 c22 by auto
      }
      ultimately have ?thesis by auto
      then show ?thesis by auto
    qed
    have block_in_list_node_b4: "block_in_list (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) curl (fst (snd (alloc b4 li lv ids (Suc curl))))"
      using block_in_list_alloc_b4 block_in_list_alloc_b4_b1 block_in_list_alloc_b4_b2 block_in_list_alloc_b4_b3 by (simp add: b2)
    have ?case using alloc_b4 list_b4 block_in_list_node_b4 by auto
    }
    moreover
    {assume c5: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have alloc_b5: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    have list_b5: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = li"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c5 by auto
    have ?case using Suc(4) alloc_b5 list_b5 by auto
    }
    ultimately have ?case by blast
  }
  moreover
  {assume xa_gr_1: "Suc xa > 1"
    have xa_lv_suc_curl: "xa = lv - Suc curl" using Suc(2) by linarith
    have de_lv_le_suc_suc_curl: "\<not> lv < Suc (Suc curl)" using xa_gr_1 xa_lv_suc_curl by auto
    have lv_gr_suc_curl: "lv > Suc curl" using xa_gr_1 xa_lv_suc_curl by auto
    have de_lv_le_suc_curl: "\<not> lv < Suc curl" using lv_gr_suc_curl by auto
    have de_lv_eq_suc_curl: "lv \<noteq> Suc curl" using lv_gr_suc_curl by auto

    {assume c11: "snd (snd (snd (alloc b1 li lv ids (Suc curl))))"
    have alloc_b11: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c11 by auto
    have list_b11: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b1 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c11 by auto

    have block_in_list_alloc_b11: "block_in_list (fst (alloc b1 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
      using Suc(1) xa_lv_suc_curl Suc(3) block_in_list_b1 de_lv_le_suc_suc_curl Suc(6)
      by (metis (full_types) block_in_list_alloc_leaf_case1 block_in_list_alloc_leaf_case3 block_in_list_alloc_leaf_case4 de_lv_eq_suc_curl tree.exhaust)
    have block_in_list_alloc_b11_b2: "block_in_list b2 (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b11_b3: "block_in_list b3 (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b11_b4: "block_in_list b4 (Suc curl) (fst (snd (alloc b1 li lv ids (Suc curl))))"
      sorry
    have block_in_list_node_b11: "block_in_list (Node (fst (alloc b1 li lv ids (Suc curl))) b2 b3 b4) curl (fst (snd (alloc b1 li lv ids (Suc curl))))"
      using block_in_list_alloc_b11 block_in_list_alloc_b11_b2 block_in_list_alloc_b11_b3 block_in_list_alloc_b11_b4 by (simp add: b2)
    have ?case using alloc_b11 list_b11 block_in_list_node_b11 by auto
    }
    moreover
    {assume c22: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl))))"
    have alloc_b22: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c22 by auto
    have list_b22: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b2 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c22 by auto

    have block_in_list_alloc_b22: "block_in_list (fst (alloc b2 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
      using Suc(1) xa_lv_suc_curl Suc(3) block_in_list_b2 de_lv_le_suc_suc_curl Suc(6)
      by (metis (full_types) block_in_list_alloc_leaf_case1 block_in_list_alloc_leaf_case3 block_in_list_alloc_leaf_case4 de_lv_eq_suc_curl tree.exhaust)
    have block_in_list_alloc_b22_b1: "block_in_list b1 (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b22_b3: "block_in_list b3 (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b22_b4: "block_in_list b4 (Suc curl) (fst (snd (alloc b2 li lv ids (Suc curl))))"
      sorry
    have block_in_list_node_b22: "block_in_list (Node b1 (fst (alloc b2 li lv ids (Suc curl))) b3 b4) curl (fst (snd (alloc b2 li lv ids (Suc curl))))"
      using block_in_list_alloc_b22 block_in_list_alloc_b22_b1 block_in_list_alloc_b22_b3 block_in_list_alloc_b22_b4 by (simp add: b2)
    have ?case using alloc_b22 list_b22 block_in_list_node_b22 by auto
    }
    moreover
    {assume c33: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl))))"
    have alloc_b33: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c33 by auto
    have list_b33: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b3 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c33 by auto

    have block_in_list_alloc_b33: "block_in_list (fst (alloc b3 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
      using Suc(1) xa_lv_suc_curl Suc(3) block_in_list_b3 de_lv_le_suc_suc_curl Suc(6)
      by (metis (full_types) block_in_list_alloc_leaf_case1 block_in_list_alloc_leaf_case3 block_in_list_alloc_leaf_case4 de_lv_eq_suc_curl tree.exhaust)
    have block_in_list_alloc_b33_b1: "block_in_list b1 (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b33_b2: "block_in_list b2 (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b33_b4: "block_in_list b4 (Suc curl) (fst (snd (alloc b3 li lv ids (Suc curl))))"
      sorry
    have block_in_list_node_b33: "block_in_list (Node b1 b2 (fst (alloc b3 li lv ids (Suc curl))) b4) curl (fst (snd (alloc b3 li lv ids (Suc curl))))"
      using block_in_list_alloc_b33 block_in_list_alloc_b33_b1 block_in_list_alloc_b33_b2 block_in_list_alloc_b33_b4 by (simp add: b2)
    have ?case using alloc_b33 list_b33 block_in_list_node_b33 by auto
    }
    moreover
    {assume c44: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl))))"
    have alloc_b44: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c44 by auto
    have list_b44: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = fst (snd (alloc b4 li lv ids (Suc curl)))"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c44 by auto

    have block_in_list_alloc_b44: "block_in_list (fst (alloc b4 li lv ids (Suc curl))) (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
      using Suc(1) xa_lv_suc_curl Suc(3) block_in_list_b4 de_lv_le_suc_suc_curl Suc(6)
      by (metis (full_types) block_in_list_alloc_leaf_case1 block_in_list_alloc_leaf_case3 block_in_list_alloc_leaf_case4 de_lv_eq_suc_curl tree.exhaust)
    have block_in_list_alloc_b44_b1: "block_in_list b1 (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b44_b2: "block_in_list b2 (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
      sorry
    have block_in_list_alloc_b44_b3: "block_in_list b3 (Suc curl) (fst (snd (alloc b4 li lv ids (Suc curl))))"
      sorry
    have block_in_list_node_b44: "block_in_list (Node b1 b2 b3 (fst (alloc b4 li lv ids (Suc curl)))) curl (fst (snd (alloc b4 li lv ids (Suc curl))))"
      using block_in_list_alloc_b44 block_in_list_alloc_b44_b1 block_in_list_alloc_b44_b2 block_in_list_alloc_b44_b3 by (simp add: b2)
    have ?case using alloc_b44 list_b44 block_in_list_node_b44 by auto
    }
    moreover
    {assume c55: "snd (snd (snd (alloc b1 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b2 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b3 li lv ids (Suc curl)))) = False \<and>
                snd (snd (snd (alloc b4 li lv ids (Suc curl)))) = False"
    have alloc_b55: "fst (alloc (Node b1 b2 b3 b4) li lv ids curl) = Node b1 b2 b3 b4"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    have list_b55: "fst (snd (alloc (Node b1 b2 b3 b4) li lv ids curl)) = li"
      unfolding alloc.simps(2) Let_def using de_lv_le_suc_curl c55 by auto
    have ?case using Suc(4) alloc_b55 list_b55 by auto
    }
    ultimately have ?case by blast
  }
  ultimately have ?case by fastforce
  then show ?case by auto
qed

lemma inv_block_in_list_alloc:
  "lv < length li \<Longrightarrow>
  block_in_list b curl li \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (alloc b li lv ids curl))) = True \<Longrightarrow>
  block_in_list (fst (alloc b li lv ids curl)) curl (fst (snd (alloc b li lv ids curl)))"
proof(induct b)
  case (Leaf x)
  then show ?case using block_in_list_alloc_leaf_case1 block_in_list_alloc_leaf_case2 block_in_list_alloc_leaf_case3 block_in_list_alloc_leaf_case4
    by metis
next
  case (Node b1 b2 b3 b4)
  then show ?case using block_in_list_alloc_node by auto
qed

lemma pool_alloc_block_in_list_case1:
  "block_in_list_valid po \<Longrightarrow>
  lv < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  block_in_list_valid (fst (pool_alloc po lv n ids))"
proof-
  assume a0: "lv < length (freelist po)"
     and a1: "block_in_list_valid po"
     and a2: "finite ids"
     and a3: "\<not> lv < 0"
     and a4: "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). block_in_list b 0 (freelist po)" using a1 block_in_list_valid_def by auto
  have p1: "block_in_list (zerolevelblocklist po ! n) 0 (freelist po)" using p0 a4 by auto
  have p2: "block_in_list (fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)) 0 (fst (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)))"
    using inv_block_in_list_alloc a0 a1 a2 a4 p1 by blast
  let ?po = "let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! n) (freelist po) lv ids 0
            in po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>"
  {
    have p3: "fst (pool_alloc po lv n ids) = ?po" apply simp using a4 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist ?po ! n) = fst (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0)" unfolding Let_def using a4 by auto
    have p5: "(freelist ?po) = fst (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))" unfolding Let_def using a4 by auto
    then have p6: "block_in_list (zerolevelblocklist ?po ! n) 0 (freelist ?po)"
      using p2 p4 p5 unfolding Let_def by auto
    with p0 have p7: "\<forall>b \<in> set (zerolevelblocklist ?po). block_in_list b 0 (freelist ?po)" unfolding Let_def apply auto
      sorry
    have p8: "block_in_list_valid ?po" unfolding block_in_list_valid_def using p7 by auto
    with p3 have p9: "block_in_list_valid (fst (pool_alloc po lv n ids))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_alloc_block_in_list_case3:
  "block_in_list_valid po \<Longrightarrow>
  lv < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  block_in_list_valid (fst (pool_alloc po lv n ids))"
  by auto

lemma pool_alloc_block_in_list_case2:
  "block_in_list_valid po \<Longrightarrow>
  lv < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> lv < 0 \<Longrightarrow>
  snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  block_in_list_valid (fst (pool_alloc po lv n ids))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith
next
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto
  have step: "pool_alloc po lv n ids = pool_alloc po lv (Suc n) ids" using Suc by auto
  { 
    assume a00: "snd (snd (snd (alloc ((zerolevelblocklist po) ! (Suc n)) (freelist po) lv ids 0))) = False \<and> (Suc n) < length (zerolevelblocklist po) - 1"
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith  
    ultimately have "block_in_list_valid (fst (pool_alloc po lv (Suc n) ids))"
      using Suc.hyps(1) Suc.prems(1) Suc.prems(2) Suc.prems(3) by blast
  }
  moreover
  have "block_in_list_valid (fst (pool_alloc po lv (Suc n) ids))"
    using Suc.prems(1) Suc.prems(2) Suc.prems(3) pool_alloc_block_in_list_case1 pool_alloc_block_in_list_case3 calculation by blast
  ultimately show ?case using step by auto
qed

lemma inv_block_in_list_pool_alloc:
  "lv < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  block_in_list_valid po \<Longrightarrow>
  block_in_list_valid (fst (pool_alloc po lv n ids))"
  apply(cases "lv < 0") apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) \<and> n < length (zerolevelblocklist po)")
  using pool_alloc_block_in_list_case1[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  apply(cases "snd (snd (snd (alloc (zerolevelblocklist po ! n) (freelist po) lv ids 0))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_alloc_block_in_list_case3[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] apply simp
  using pool_alloc_block_in_list_case2[where po = "po" and lv = "lv" and n = "n" and ids = "ids"] by simp

lemma inv_block_in_list_k_mem_pool_alloc_helper1:
  "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> lv < length (freelist po) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_block_in_list"
proof-
  assume a0: "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> lv < length (freelist po)"
  hence p0: "(\<forall>p \<in> set (pools s). block_in_list_valid p)"
    by (simp add: inv_block_in_list_def)
  hence p1: "block_in_list_valid po"
    by (simp add: a0)
  hence p2: "finite (idset s)"
    by (simp add: a0)
  hence p3: "lv < length (freelist po)"
    by (simp add: a0)
  let ?rpi = "pool_alloc po lv 0 (idset s)"
  have p3: "block_in_list_valid (fst ?rpi)" using inv_block_in_list_pool_alloc p3 p2 p1 by blast
  moreover
  have p3: "\<forall>p \<in> set ((remove1 po (pools s)) @ [fst ?rpi]). block_in_list_valid p" using p0 p3 by auto
  let ?s = "s\<lparr>pools := remove1 po (pools s) @ [fst ?rpi], idset := fst (snd ?rpi)\<rparr>"
  have p4: "?s \<in> inv_block_in_list"
    unfolding inv_block_in_list_def using p3 by auto
  then show "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> lv < length (freelist po) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)) \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_block_in_list"
    by (smt fst_conv)
qed

lemma inv_block_in_list_k_mem_pool_alloc_helper3:
  "s \<in> inv_block_in_list \<Longrightarrow>
    \<not> snd (snd (let zeroli = zerolevelblocklist po; aa = alloc (zeroli ! 0) (freelist po) lv (idset s) 0; re = snd (snd (snd aa))
                 in if re \<and> zeroli \<noteq> [] then (po\<lparr>zerolevelblocklist := zeroli[0 := fst aa], freelist := fst (snd aa)\<rparr>, fst (snd (snd aa)), True)
                    else if re = False \<and> 0 < length zeroli - 1 then pool_alloc po lv (Suc 0) (idset s) else (po, idset s, False))) \<Longrightarrow>
    schedule (case cur s of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> name po)\<rparr>)) \<in> inv_block_in_list"
proof-
  assume "s \<in> inv_block_in_list"
  hence p0: "(\<forall>p \<in> set (pools s). \<forall>b\<in>set (zerolevelblocklist p). block_in_list b 0 (freelist p))"
    using inv_block_in_list_def block_in_list_valid_def by blast
  let ?t = "case (cur s) of None \<Rightarrow> s
                    | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := (waitq s)(th \<mapsto> name po)\<rparr>)"
  {
    have p1: "pools s = pools ?t" by (simp add: option.case_eq_if)
    with p0 have p2: "(\<forall>p \<in> set (pools ?t). \<forall>b\<in>set (zerolevelblocklist p). block_in_list b 0 (freelist p))" by simp
    from p2 have p3: "?t \<in> inv_block_in_list"
      by (simp add: inv_block_in_list_def block_in_list_valid_def)
    from p3 have p4: "schedule ?t \<in> inv_block_in_list" by (simp add:inv_block_in_list_schedule)
  }
  then show ?thesis unfolding inv_block_in_list_def
    by blast
qed

lemma inv_block_in_list_k_mem_pool_alloc_helper2:
  "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> lv < length (freelist po) \<Longrightarrow>
    \<not> lv < 0 \<Longrightarrow>
    snd (snd (pool_alloc po lv 0 (idset s))) \<noteq> True \<Longrightarrow>
    fst (if lv < 0 then (s, False)
         else let ts = t_state s; ps = pools s; wq = waitq s; cu = cur s; ids = idset s; rpi = pool_alloc po lv 0 ids
              in if snd (snd rpi) = True then (s\<lparr>pools := remove1 po ps @ [fst rpi], idset := fst (snd rpi)\<rparr>, True)
                 else if snd (snd rpi) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)
                      then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> name po)\<rparr>)
                           in (schedule t, False)
                      else (s, False))
    \<in> inv_block_in_list"
  apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
   prefer 2
   apply blast               
  apply(simp add:inv_block_in_list_schedule)
  using inv_block_in_list_k_mem_pool_alloc_helper3 by auto

lemma inv_block_in_list_k_mem_pool_alloc: "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> lv < length (freelist po)
                                           \<Longrightarrow> fst (k_mem_pool_alloc s po lv ti) \<in> inv_block_in_list" 
proof (induct ti)
  case WAIT
  then show ?case unfolding k_mem_pool_alloc_def
    apply(case_tac "lv < 0")
     apply(simp add:Let_def)
    apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = True")
       apply(case_tac "snd (snd (pool_alloc po lv 0 (idset s))) = False \<and> (WAIT = WAIT \<or> WAIT = FOREVER)")
      apply(simp add:Let_def)
    using inv_block_in_list_k_mem_pool_alloc_helper1 inv_block_in_list_k_mem_pool_alloc_helper2 snd_conv by auto
  case FOREVER
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_block_in_list\<close> k_mem_pool_alloc_def option.case_eq_if)
  case NO_WAIT
  then show ?case unfolding k_mem_pool_alloc_def Let_def
    by (smt State.surjective State.update_convs(2) State.update_convs(6) \<open>fst (k_mem_pool_alloc s po lv WAIT) \<in> inv_block_in_list\<close> fst_conv k_mem_pool_alloc_def timeout_state_type.distinct(1) timeout_state_type.distinct(5))
qed

lemma inv_block_in_list_free_leaf:
  "block_in_list (Leaf x) curl li \<Longrightarrow>
  curl < length li \<Longrightarrow>
  finite ids \<Longrightarrow>
  fst (snd x) = ALLOC \<Longrightarrow> 
  num = snd (snd x) \<Longrightarrow> 
  block_in_list (fst (free (Leaf x) li num ids)) curl (fst (snd (free (Leaf x) li num ids)))"
proof-
  assume a0: "block_in_list (Leaf x) curl li"
     and a1: "curl < length li"
     and a2: "finite ids"
     and a3: "fst (snd x) = ALLOC"
     and a4: "num = snd (snd x)"
  have p0: "fst x = curl"
    using a0 block_in_list_leaf_node(1) by blast
  have p1: "(fst (free (Leaf x) li num ids)) = (Leaf (fst x, FREE, snd (snd x)))"
    using a3 a4 free.simps(1) by auto
  have p2: "(fst (snd (free (Leaf x) li num ids))) = li[curl:=(li ! curl) \<union> {snd (snd x)}]"
    using a3 a4 free.simps(1) p0 by auto
  have p3: "get_blocktype (Leaf (fst x, FREE, snd (snd x))) = FREE"
    unfolding get_blocktype_def by auto
  have p4: "snd (snd x) \<in> li[curl:=(li ! curl) \<union> {snd (snd x)}] ! curl"
    using a1 by auto
  show ?thesis using p1 p2 p0 p3 p4 b1 by auto
qed

lemma inv_block_in_list_free:
  "block_in_list b curl li \<Longrightarrow>
  curl < length li \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (free b li num ids))) = True \<Longrightarrow>
  block_in_list (fst (free b li num ids)) curl (fst (snd (free b li num ids)))"
proof(induct b)
  case (Leaf x)
  then show ?case
    apply auto
    using inv_block_in_list_free_leaf by auto
next
  case (Node b1 b2 b3 b4)
  then show ?case sorry
qed

lemma pool_free_block_in_list_case1:
  "block_in_list_valid po \<Longrightarrow>
  0 < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po) \<Longrightarrow>
  block_in_list_valid (fst (pool_free po num n ids))"
proof-
  assume a0: "block_in_list_valid po"
     and a1: "0 < length (freelist po)"
     and a2: "finite ids"
     and a3: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)"
  have p0: "\<forall>b \<in> set (zerolevelblocklist po). block_in_list b 0 (freelist po)" using a0 block_in_list_valid_def by auto
  have p1: "block_in_list (zerolevelblocklist po ! n) 0 (freelist po)" using p0 a3 by auto
  have p2: "block_in_list (fst (free (zerolevelblocklist po ! n) (freelist po) num ids)) 0 (fst (snd (free (zerolevelblocklist po ! n) (freelist po) num ids)))"
    using p1 a1 a2 a3 inv_block_in_list_free by auto
  let ?po = "let zeroli = zerolevelblocklist po; aa = free (zeroli ! n) (freelist po) num ids
            in po\<lparr>zerolevelblocklist := zeroli[n := fst aa], freelist := fst (snd aa)\<rparr>"
  {
    have p3: "fst (pool_free po num n ids) = ?po" apply simp using a3 Let_def by (smt fst_conv)
    moreover
    have p4: "(zerolevelblocklist ?po ! n) = fst (free (zerolevelblocklist po ! n) (freelist po) num ids)"
      unfolding Let_def using a3 by auto
    have p5: "freelist ?po = (fst (snd (free (zerolevelblocklist po ! n) (freelist po) num ids)))"
      unfolding Let_def using a3 by auto
    then have p6: "block_in_list (zerolevelblocklist ?po ! n) 0 (freelist ?po)" using p2 p4 p5 unfolding Let_def by auto
    with p0 have p7: "\<forall>b \<in> set (zerolevelblocklist ?po). block_in_list b 0 (freelist ?po)" unfolding Let_def apply auto
      sorry
    have p8: "block_in_list_valid ?po" unfolding block_in_list_valid_def using p7 by auto
    with p3 have p9: "block_in_list_valid (fst (pool_free po num n ids))" by auto
  }
  then show ?thesis by auto
qed

lemma pool_free_block_in_list_case3:
  "block_in_list_valid po \<Longrightarrow>
  0 < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = True \<and> n < length (zerolevelblocklist po)) \<Longrightarrow>
  \<not> (snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1) \<Longrightarrow>
  block_in_list_valid (fst (pool_free po num n ids))"
  by auto

lemma pool_free_block_in_list_case2:
  "block_in_list_valid po \<Longrightarrow>
  0 < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  snd (snd (snd (free (zerolevelblocklist po ! n) (freelist po) num ids))) = False \<and> n < length (zerolevelblocklist po) - 1 \<Longrightarrow>
  block_in_list_valid (fst (pool_free po num n ids))"
proof(induct "(length (zerolevelblocklist po) - n)" arbitrary: n )
  case 0
  then show ?case by linarith 
next 
  case (Suc k)
  then have len: "length (zerolevelblocklist po) > 0" by auto     
  have step: "pool_free po num n ids = pool_free po num (Suc n) ids" using Suc by auto
  { 
    assume a00: "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1) "
    moreover 
    have "length (zerolevelblocklist po) - Suc n = k"
      using Suc.hyps(2) by linarith   
    ultimately have "block_in_list_valid (fst (pool_free po num (Suc n) ids))"
      using Suc.hyps(1) Suc.prems(1) pool_free_block_in_list_case1 pool_free_block_in_list_case3
      proof -
        { assume "Suc n < length (zerolevelblocklist po) - 1 \<and> \<not> snd (snd (snd (free (zerolevelblocklist po ! Suc n) (freelist po) num ids)))"
          then have ?thesis
            using Suc.prems(2) Suc.prems(3) \<open>\<And>na. \<lbrakk>k = length (zerolevelblocklist po) - na; block_in_list_valid po; 0 < length (freelist po); finite ids; snd (snd (snd (free (zerolevelblocklist po ! na) (freelist po) num ids))) = False \<and> na < length (zerolevelblocklist po) - 1\<rbrakk> \<Longrightarrow> block_in_list_valid (fst (pool_free po num na ids))\<close> \<open>block_in_list_valid po\<close> \<open>length (zerolevelblocklist po) - Suc n = k\<close> by blast }
        then show ?thesis
          by (metis (full_types) Suc.prems(2) Suc.prems(3) \<open>block_in_list_valid po\<close> pool_free_block_in_list_case1 pool_free_block_in_list_case3)
      qed
  }    
  moreover 
  have "block_in_list_valid (fst (pool_free po num (Suc n) ids))"
    using Suc.prems(2) calculation Suc.prems(4) by blast 
  ultimately show ?case using step by auto
qed

lemma inv_block_in_list_pool_free:
  "block_in_list_valid po \<Longrightarrow>
  0 < length (freelist po) \<Longrightarrow>
  finite ids \<Longrightarrow>
  block_in_list_valid (fst (pool_free po num n ids))"
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = True \<and> n < length (zerolevelblocklist po)")
  using pool_free_block_in_list_case1[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  apply(cases "(snd (snd (snd (free ((zerolevelblocklist po) ! n) (freelist po) num ids)))) = False \<and> n < (length (zerolevelblocklist po) - 1)")
   prefer 2
  using pool_free_block_in_list_case3[where po = "po" and num = "num" and n = "n" and ids = "ids"] apply simp
  using pool_free_block_in_list_case2[where po = "po" and num = "num" and n = "n" and ids = "ids"] by simp

lemma inv_block_in_list_k_mem_pool_free: "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> 0 < length (freelist po)
                                           \<Longrightarrow> fst (k_mem_pool_free s po num) \<in> inv_block_in_list"
proof-
  assume a0: "po \<in> set (pools s) \<and> s \<in> inv_block_in_list \<and> finite (idset s) \<and> 0 < length (freelist po)"
  hence p0: "(\<forall>p \<in> set (pools s). block_in_list_valid p)" unfolding inv_block_in_list_def by auto
  from a0 p0 have p1: "block_in_list_valid po" by simp
  let ?po1 = "fst (pool_free po num 0 (idset s))"
  from p1 have p2: "block_in_list_valid ?po1"
    using inv_block_in_list_pool_free[where po = "po" and num = "num" and n = 0 and ids = "idset s"] a0 by auto
  let ?t = "fst (k_mem_pool_free s po num)"
  {
    have p3: "set (pools ?t) = set (append (remove1 po (pools s)) [?po1])"
      unfolding k_mem_pool_free_def
      apply(case_tac "snd (snd (pool_free po num 0 (idset s))) = True")
       apply(case_tac "{t. (waitq s) t = Some (name po)} \<noteq> {}")
        apply(simp add:Let_def)
       apply(simp add:Let_def)
      using inv_block_k_mem_pool_free_helper[of po num s]
      pool_free_lm[where po = "po" and num = "num" and n = 0 and ids = "idset s" and re="pool_free po num 0 (idset s)"]
      set_helper[of po "pools s"]
      snd_conv fst_conv a0 by simp
    fix pl
    assume a1: "pl \<in> set (pools ?t)" 
    have p4: "block_in_list_valid pl"
      proof(cases "pl = ?po1")
        assume "pl = ?po1"
        with p2 show ?thesis by simp
      next
        assume "pl \<noteq> ?po1"
        with p0 p3 a1 show ?thesis by force
      qed
  }
  then show ?thesis unfolding inv_block_in_list_def by force
qed
*)
subsection \<open>def and proof of inv_block_in_list\<close>

fun collect_freeleaf :: "Block \<Rightarrow> Block set"
  where "collect_freeleaf (Leaf x) = (if fst (snd x) = FREE then {(Leaf x)}
                                       else {})" |
        "collect_freeleaf (Node n1 n2 n3 n4) = collect_freeleaf n1 \<union> collect_freeleaf n2 \<union> collect_freeleaf n3 \<union> collect_freeleaf n4"

definition pool_freelist :: "Pool \<Rightarrow> Level_Freeset"
  where "pool_freelist po \<equiv> (THE li. length li = n_levels po \<and>
                                     (\<forall>b \<in> set (zerolevelblocklist po). \<forall>x \<in> collect_freeleaf b. get_blockid x \<in> li ! get_blocklevel x))"

definition "inv_block_in_list \<equiv> {s::State. (\<forall>p \<in> set (pools s). pool_freelist p = freelist p)}"

lemma inv_block_in_list_s0: "s0 \<in> inv_block_in_list"
  unfolding s0_def inv_block_in_list_def using s0_def poolsinit by auto

lemma inv_block_in_list_time_tick: "s \<in> inv_block_in_list \<Longrightarrow> time_tick s \<in> inv_block_in_list"
  unfolding time_tick_def Let_def inv_block_in_list_def by auto
         
lemma inv_block_in_list_schedule: "s \<in> inv_block_in_list \<Longrightarrow> schedule s \<in> inv_block_in_list"
  unfolding schedule_def Let_def inv_block_in_list_def
  by (simp add: option.case_eq_if)

end