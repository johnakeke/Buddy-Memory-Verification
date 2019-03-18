theory Memory_Allocation_Security
imports Memory_Allocation_Model Memory_Allocation_Invariant
begin

subsection \<open>def of Memory Execution Model\<close>

typedecl Thread
datatype thread_state_type = READY | RUNNING | BLOCKED
datatype timeout_state_type = WAIT | NO_WAIT

record State = t_state :: "Thread \<Rightarrow> thread_state_type"
               pools :: "Pool set"
               waitq :: "Thread \<rightharpoonup> poolname"
               cur :: "Thread option"
               idset :: "ID set"

definition schedule :: "State \<Rightarrow> State"
  where "schedule s \<equiv>
          let t = cur s;
              news = (case t of None \<Rightarrow> s
                              | Some th \<Rightarrow> s\<lparr>t_state := (t_state s)(th := READY)\<rparr>);
              readyset = {t. (t_state news t) = READY} in
          if readyset = {} then s
          else let newcur = SOME p. p \<in> readyset in
               news\<lparr>t_state := (t_state news)(newcur := RUNNING),cur := Some newcur\<rparr>"

definition k_mem_pool_alloc :: "State \<Rightarrow> Pool \<Rightarrow> nat \<Rightarrow> timeout_state_type \<Rightarrow> (State \<times> bool)"
  where "k_mem_pool_alloc s po lv ti \<equiv>
           let ts = t_state s;
               ps = pools s - {po};
               wq = waitq s;
               cu = cur s;
               ids = idset s;
               rpi = alloc (zerolevelblocks po) lv ids;
               newpo = po\<lparr>zerolevelblocks := fst rpi\<rparr> in
           if snd (snd rpi) = True then
             (s\<lparr>pools := ps \<union> {newpo},
               idset := fst (snd rpi)\<rparr>, True)
           else if snd (snd rpi) = False \<and> ti = WAIT then
              let t = (case cu of None \<Rightarrow> s
                                | Some th \<Rightarrow> s\<lparr>t_state := ts(th := BLOCKED),
                                              waitq := wq(th := Some (pname po)),
                                              cur := None\<rparr>) in
              (schedule t, False)
           else
             (s, False)"

definition k_mem_pool_free :: "State \<Rightarrow> Pool \<Rightarrow> Block \<Rightarrow> (State \<times> bool)"
  where "k_mem_pool_free s po b \<equiv> 
          let ts = t_state s;
              ps = pools s - {po};
              wq = waitq s;
              ids = idset s;
              npi = free (zerolevelblocks po) b ids;
              newpo = po\<lparr>zerolevelblocks := fst npi\<rparr> in
           if snd (snd npi) = True then
             let wqth = {t. wq t = Some (pname po)} in
             if wqth \<noteq> {} then
               (s\<lparr>t_state := (\<lambda>t. (if (t \<in> wqth) then READY else (ts t))),
                  pools := ps \<union> {newpo},
                  waitq := (\<lambda>t. (if (t \<in> wqth) then None else (wq t))),
                  idset := fst (snd npi)\<rparr>, True)
             else
               (s\<lparr>pools := ps \<union> {newpo},
                  idset := fst (snd npi)\<rparr>, True)
           else
             (s, False)"

subsection \<open>def and proof of inv_cur_state and inv_waitq_state\<close>

definition "inv_cur_waitq \<equiv> {s::State. (\<forall>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING) \<and> (\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED)}"

lemma inv_cur_waitq_schedule: "s \<in> inv_cur_waitq \<Longrightarrow> schedule s \<in> inv_cur_waitq"
proof (cases "{t. t_state (case (cur s) of None \<Rightarrow> s | Some th \<Rightarrow> s\<lparr>t_state := (t_state s)(th := READY)\<rparr>) t = READY} = {}")
  case True
  assume a0: "s \<in> inv_cur_waitq"
  have p0: "schedule s = s" unfolding schedule_def Let_def
    by (simp add: True)
  have p1: "schedule s \<in> inv_cur_waitq"
    by (simp add: a0 p0)
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
    by (smt State.select_convs(1) State.select_convs(4) State.surjective State.update_convs(1) State.update_convs(4) fun_upd_same mem_Collect_eq option.simps(1))
qed

lemma inv_cur_waitq_k_mem_pool_alloc_helper1:
  "s \<in> inv_cur_waitq \<Longrightarrow>
    snd (snd (alloc (zerolevelblocks po) lv (idset s))) = True \<Longrightarrow>
    \<not> (snd (snd (alloc (zerolevelblocks po) lv (idset s))) = False \<and> WAIT = WAIT) \<Longrightarrow>
    fst (let ts = t_state s; ps = pools s - {po}; wq = waitq s; cu = cur s; ids = idset s; rpi = alloc (zerolevelblocks po) lv ids;
             newpo = po\<lparr>zerolevelblocks := fst rpi\<rparr>
         in if snd (snd rpi) = True then (s\<lparr>pools := ps \<union> {newpo}, idset := fst (snd rpi)\<rparr>, True)
            else if snd (snd rpi) = False \<and> WAIT = WAIT
                 then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> pname po)\<rparr>) in (schedule t, False)
                 else (s, False))
    \<in> inv_cur_waitq"
  unfolding inv_cur_waitq_def
  by (smt State.select_convs(1) State.select_convs(3) State.select_convs(4) State.surjective State.update_convs(2) State.update_convs(5) fst_conv mem_Collect_eq)

lemma inv_cur_waitq_k_mem_pool_alloc_helper3:
  "s \<in> inv_cur_waitq \<Longrightarrow>
    \<not> snd (snd (alloc (zerolevelblocks po) lv (idset s))) \<Longrightarrow>
    schedule (case cur s of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> pname po)\<rparr>)) \<in> inv_cur_waitq"
proof-
  assume "s \<in> inv_cur_waitq"
  hence p0: "\<exists>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING"
    and p1: "\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED"
    apply (simp add: inv_cur_waitq_def)
    using \<open>s \<in> inv_cur_waitq\<close> inv_cur_waitq_def by auto
  let ?t = "(case cur s of None \<Rightarrow> s
            | Some th \<Rightarrow> (s\<lparr>t_state := (t_state s)(th := BLOCKED), waitq := waitq s(th \<mapsto> pname po),cur := None\<rparr>))"
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
    snd (snd (alloc (zerolevelblocks po) lv (idset s))) \<noteq> True \<Longrightarrow>
    fst (let ts = t_state s; ps = pools s - {po}; wq = waitq s; cu = cur s; ids = idset s; rpi = alloc (zerolevelblocks po) lv ids;
             newpo = po\<lparr>zerolevelblocks := fst rpi\<rparr>
         in if snd (snd rpi) = True then (s\<lparr>pools := ps \<union> {newpo}, idset := fst (snd rpi)\<rparr>, True)
            else if snd (snd rpi) = False \<and> WAIT = WAIT
                 then let t = case cu of None \<Rightarrow> s | Some th \<Rightarrow> cur_update Map.empty (s\<lparr>t_state := ts(th := BLOCKED), waitq := wq(th \<mapsto> pname po)\<rparr>) in (schedule t, False)
                 else (s, False))
    \<in> inv_cur_waitq"
  apply(case_tac "snd (snd (alloc (zerolevelblocks po) lv (idset s))) = False \<and> WAIT = WAIT")
   prefer 2
   apply blast
  apply(simp add:inv_cur_waitq_schedule)
  using inv_cur_waitq_k_mem_pool_alloc_helper3 by blast

lemma inv_cur_waitq_k_mem_pool_alloc: "s \<in> inv_cur_waitq \<Longrightarrow> fst (k_mem_pool_alloc s po lv ti) \<in> inv_cur_waitq" 
proof (induct ti)
  case WAIT
  then show ?case unfolding k_mem_pool_alloc_def
    apply(case_tac "snd (snd (alloc (zerolevelblocks po) lv (idset s))) = True")
     apply(case_tac "snd (snd (alloc (zerolevelblocks po) lv (idset s))) = False \<and> WAIT = WAIT")
      apply(simp add:Let_def)
    using inv_cur_waitq_k_mem_pool_alloc_helper1 inv_cur_waitq_k_mem_pool_alloc_helper2 snd_conv
    unfolding Let_def by simp+
  case NO_WAIT
    then show ?case unfolding k_mem_pool_alloc_def Let_def
      by (simp add: inv_cur_waitq_def)
  qed
                                                                         
lemma inv_cur_waitq_k_mem_pool_free: "s \<in> inv_cur_waitq \<Longrightarrow> fst (k_mem_pool_free s po b) \<in> inv_cur_waitq"
proof -
  assume a0: "s \<in> inv_cur_waitq"
  hence p0: "\<forall>t. cur s = Some t \<longrightarrow> t_state s t = RUNNING"
    and p1: "\<forall>th. waitq s th \<noteq> None \<longrightarrow> t_state s th = BLOCKED"
    unfolding inv_cur_waitq_def by auto
  let ?t = "fst (k_mem_pool_free s po b)"
  {
    have p2: "\<forall>t. t_state s t = READY \<longrightarrow> waitq s t = None" using p1 by auto
    have p3: "\<forall>t. cur s = Some t \<longrightarrow> waitq s t = None" using p0 p1 by auto
    have p4: "\<forall>t. cur ?t = Some t \<longrightarrow> waitq s t = None" using p2 p3 unfolding k_mem_pool_free_def Let_def by simp
    have p5: "\<forall>t. cur ?t = Some t \<longrightarrow> t_state ?t t = RUNNING" using p0 p4 fst_conv unfolding k_mem_pool_free_def Let_def
      by (smt State.ext_inject State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(5) mem_Collect_eq option.distinct(1))
    fix th
    assume a1: "waitq ?t th \<noteq> None"
    have p6: "waitq s th \<noteq> None" unfolding k_mem_pool_free_def Let_def using a1 k_mem_pool_free_def
      by (smt State.ext_inject State.surjective State.update_convs(2) State.update_convs(3) State.update_convs(5) prod.collapse prod.inject)
    have p7: "t_state s th = BLOCKED" using p1 p6 by simp
    have p8: "t_state ?t th = BLOCKED" using a1 p7 fst_conv unfolding k_mem_pool_free_def Let_def
      by (smt State.ext_inject State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(5))
    have p9: "(\<forall>t. cur ?t = Some t \<longrightarrow> t_state ?t t = RUNNING) \<and> (\<forall>th. waitq ?t th \<noteq> None \<longrightarrow> t_state ?t th = BLOCKED)"
      using p5 a1 p8 p1 fst_conv unfolding k_mem_pool_free_def Let_def
      by (smt State.ext_inject State.surjective State.update_convs(1) State.update_convs(2) State.update_convs(3) State.update_convs(5))
  }       
  then show ?thesis using p0 p1 unfolding inv_cur_waitq_def k_mem_pool_free_def Let_def by auto
qed

end