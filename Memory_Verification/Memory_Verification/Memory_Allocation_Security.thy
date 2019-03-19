theory Memory_Allocation_Security
imports Memory_Allocation_Model Memory_Allocation_Invariant SK_SecurityModel "HOL-Library.Multiset"
begin

subsection \<open>Memory Execution Model\<close>

type_synonym partition_id = nat
type_synonym partition_name = string
datatype Partition_Conf = PartConf partition_id partition_name
type_synonym Partitions = "partition_id \<rightharpoonup> Partition_Conf"

type_synonym domain_id = nat
type_synonym Mem_Add = "nat multiset"
type_synonym Partition_Mem = "partition_id \<rightharpoonup> Mem_Add"

record Sys_Config = partconf :: Partitions
                    scheduler :: domain_id

record State = current :: domain_id 
               partitionmem :: Partition_Mem
               mempools :: "Pool set"
               memids :: "ID set"

datatype Hypercall = Buddy_Memory_Alloc Pool nat |
                     Buddy_Memory_Free Pool Block nat
datatype System_Event = Schedule
datatype Event = hyperc Hypercall | sys System_Event

primrec get_partname_by_type :: "Partition_Conf \<Rightarrow> partition_name"
  where "get_partname_by_type (PartConf _ pn) = pn"
                                                                           
primrec get_partid_by_type :: "Partition_Conf \<Rightarrow> partition_id"
  where "get_partid_by_type (PartConf pid _) = pid"

definition is_a_partition :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_partition sc nid \<equiv> (partconf sc) nid \<noteq> None"

definition is_a_scheduler :: "Sys_Config \<Rightarrow> domain_id \<Rightarrow> bool"
  where "is_a_scheduler sc nid \<equiv> (scheduler sc) = nid"

definition get_partconf_byid :: "Sys_Config \<Rightarrow> partition_id \<Rightarrow> Partition_Conf option"
  where "get_partconf_byid sc pid \<equiv> (partconf sc) pid"

definition get_partmem_byid :: "State \<Rightarrow> partition_id \<Rightarrow> Mem_Add option"
  where "get_partmem_byid s pid \<equiv> (partitionmem s) pid"

definition alloc_memory :: "Sys_Config \<Rightarrow> State \<Rightarrow> Pool \<Rightarrow> nat \<Rightarrow> State"
  where "alloc_memory sc s po lv \<equiv>
           (if get_partconf_byid sc (current s) \<noteq> None then
               (let partmem = get_partmem_byid s (current s);
                    re = alloc (zerolevelblocks po) lv (memids s) in
                    (if fst (snd (snd re)) = True then
                        s\<lparr>partitionmem := (partitionmem s)(current s := Some (the partmem + {#lv#}  )  ),
                          mempools := (mempools s - {po}) \<union> {po\<lparr>zerolevelblocks := fst re\<rparr>},
                          memids := fst (snd re)\<rparr>
                     else s))
            else s)"

definition free_memory :: "Sys_Config \<Rightarrow> State \<Rightarrow> Pool \<Rightarrow> Block \<Rightarrow> nat \<Rightarrow> State"
  where "free_memory sc s po b lv \<equiv>
           let partmem = get_partmem_byid s (current s) in
             (if get_partconf_byid sc (current s) \<noteq> None \<and> partmem \<noteq> None \<and> lv \<in># the partmem then
                 (let re = free (zerolevelblocks po) b lv (memids s) in
                      (if snd (snd re) = True then
                          s\<lparr>partitionmem := (partitionmem s)(current s := Some (the partmem - {#lv#})),
                            mempools := (mempools s - {po}) \<union> {po\<lparr>zerolevelblocks := fst re\<rparr>},
                            memids := fst (snd re)\<rparr>
                       else s))
              else s)"

definition schedule :: "Sys_Config \<Rightarrow> State \<Rightarrow> State set" where
  "schedule sc s \<equiv> {s\<lparr>current:= SOME p. p\<in>{x. (partconf sc) x \<noteq> None}\<rparr>}"

definition sys_config_witness :: Sys_Config 
  where "sys_config_witness \<equiv> \<lparr>partconf = Map.empty,
                               scheduler = 0\<rparr>"

consts sysconf :: "Sys_Config"
specification(sysconf)
  part_id_conf: "\<forall>p. (partconf sysconf) p \<noteq> None \<longrightarrow> get_partid_by_type (the ((partconf sysconf) p)) = p"
  part_not_sch: "(partconf sysconf) x \<noteq> None \<longrightarrow> x \<noteq> scheduler sysconf"
  sch_not_part: "scheduler sysconf = x \<longrightarrow> (partconf sysconf) x = None"
  by (metis Sys_Config.select_convs(1) sys_config_witness_def)

definition state_witness :: State
  where "state_witness \<equiv> \<lparr>current = (SOME x. (partconf sysconf) x \<noteq> None),
                          partitionmem = (\<lambda> p. (case ((partconf sysconf) p) of None \<Rightarrow> None
                                                                             | Some (PartConf _ _) \<Rightarrow> Some {#})),
                          mempools = {},
                          memids = {}\<rparr>"

consts s0t :: State
specification(s0t)
  current_part: "(partconf sysconf) (current s0t) \<noteq> None"
  part_mem_diff: "\<forall>p1 p2. p1 \<noteq> p2 \<and> get_partconf_byid sysconf p1 \<noteq> None \<and> get_partconf_byid sysconf p2 \<noteq> None \<and>
                          get_partmem_byid s0t p1 \<noteq> None \<and> get_partmem_byid s0t p2 \<noteq> None \<longrightarrow>
                          the (get_partmem_byid s0t p1) = the (get_partmem_byid s0t p2)"
  mem_name_diff: "\<forall>m1 m2. m1 \<noteq> m2 \<and> m1 \<in> mempools s0t \<and> m1 \<in> mempools s0t \<longrightarrow>
                          pname m1 \<noteq> pname m2"
  mem_ids_diff: "\<forall>m. m \<in> mempools s0t \<longrightarrow> diff_ids_valid (zerolevelblocks m)"
  sorry

primrec event_enabled :: "State \<Rightarrow> Event \<Rightarrow> bool"
  where "event_enabled s (hyperc h) = (is_a_partition sysconf (current s))" |
        "event_enabled s (sys h) =  (case h of Schedule \<Rightarrow> True)" 

definition exec_event :: "Event \<Rightarrow> (State \<times> State) set"
  where "exec_event e = {(s, s'). s' \<in> (if event_enabled s e then
                                           (case e of hyperc (Buddy_Memory_Alloc po lv) \<Rightarrow> {(alloc_memory sysconf s po lv)} |
                                                      hyperc (Buddy_Memory_Free po b lv) \<Rightarrow> {(free_memory sysconf s po b lv)} |
                                                      sys Schedule \<Rightarrow> schedule sysconf s)
                                        else {s})}"

primrec domain_of_event :: "State \<Rightarrow> Event \<Rightarrow> domain_id option"
where "domain_of_event s (hyperc h) = Some (current s)" |
      "domain_of_event s (sys h) = Some (scheduler sysconf)"

definition interference1 :: "domain_id \<Rightarrow> domain_id \<Rightarrow> bool" ("(_ \<leadsto> _)")
  where "interference1 d1 d2 \<equiv>
            if d1 = d2 then True
            else if is_a_scheduler sysconf d1 then True
            else False"

definition non_interference1 :: "domain_id \<Rightarrow> domain_id \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)")
      where "(u \<setminus>\<leadsto>  v) \<equiv> \<not> (u \<leadsto> v)"

declare non_interference1_def [cong] and interference1_def [cong] and domain_of_event_def[cong] and
       event_enabled_def[cong] and is_a_partition_def[cong] and is_a_scheduler_def[cong]

lemma nintf_neq: "u \<setminus>\<leadsto>  v \<Longrightarrow> u \<noteq> v"  by auto

lemma nintf_reflx: "interference1 u u" by auto

definition vpeq_part :: "State \<Rightarrow> partition_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_part s d t \<equiv> (partitionmem s) d = (partitionmem t) d"

definition vpeq_sched :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool"
  where "vpeq_sched s d t \<equiv> current s = current t"

definition vpeq1  :: "State \<Rightarrow> domain_id \<Rightarrow> State \<Rightarrow> bool" ("(_ \<sim> _ \<sim> _)") 
  where "vpeq1 s d t \<equiv>  
         (if d = scheduler sysconf then 
            (vpeq_sched s d t)
          else if is_a_partition sysconf d then 
            (vpeq_part s d t)
          else True)"

declare vpeq_part_def [cong] and vpeq_sched_def[cong] and vpeq1_def[cong] 

lemma vpeq_part_transitive_lemma : "\<forall> s t r d. vpeq_part s d t \<and> vpeq_part t d r \<longrightarrow> vpeq_part s d r"
  by auto

lemma vpeq_part_symmetric_lemma:"\<forall> s t d. vpeq_part s d t \<longrightarrow> vpeq_part t d s"
  by auto

lemma vpeq_part_reflexive_lemma:"\<forall> s d. vpeq_part s d s"
  by auto

lemma vpeq_scheduler_transitive_lemma : "\<forall> s t r d. vpeq_sched s d t \<and> vpeq_sched t d r \<longrightarrow> vpeq_sched s d r"
 by simp

lemma vpeq_scheduler_symmetric_lemma:"\<forall> s t d. vpeq_sched s d t \<longrightarrow> vpeq_sched t d s"
  by simp

lemma vpeq_scheduler_reflexive_lemma:"\<forall> s d. vpeq_sched s d s"
  by simp

lemma vpeq1_transitive_lemma : "\<forall> s t r d. (vpeq1 s d t) \<and> (vpeq1 t d r) \<longrightarrow> (vpeq1 s d r)"
  by auto

lemma vpeq1_symmetric_lemma : "\<forall> s t d. (vpeq1 s d t) \<longrightarrow> (vpeq1 t d s)"
  by auto

lemma vpeq1_reflexive_lemma : "\<forall> s d. (vpeq1 s d s)"
  by auto

lemma sched_current_lemma : "\<forall>s t a. vpeq1 s (scheduler sysconf) t \<longrightarrow> (domain_of_event s a) = (domain_of_event t a)"
  by (metis (no_types) Event.exhaust domain_of_event.simps(1) domain_of_event.simps(2) vpeq1_def vpeq_sched_def)
  
lemma schedeler_intf_all_help : "\<forall>d. interference1 (scheduler sysconf) d"
  by (meson interference1_def is_a_scheduler_def)

lemma no_intf_sched_help : "\<forall>d. interference1 d (scheduler sysconf) \<longrightarrow> d = (scheduler sysconf)"
  by (simp add: interference1_def is_a_scheduler_def)

lemma reachable_top: "\<forall>s a. (SM.reachable0 s0t exec_event) s \<longrightarrow> (\<exists>s'. (s, s') \<in> exec_event a)"
  proof -
  {
    fix s a
    assume p0: "(SM.reachable0 s0t exec_event) s"
    have "\<exists>s'. (s, s') \<in> exec_event a"
      proof(induct a)
        case (hyperc x) show ?case 
          apply (induct x)
          by (simp add:exec_event_def)+
        next
        case (sys x) then show ?case
          apply (induct x)
          by (simp add:exec_event_def schedule_def)+
      qed        
  }
  then show ?thesis by auto
  qed

interpretation SM_enabled
    s0t exec_event domain_of_event "scheduler sysconf" vpeq1 interference1 
  using vpeq1_transitive_lemma vpeq1_symmetric_lemma vpeq1_reflexive_lemma sched_current_lemma
        schedeler_intf_all_help no_intf_sched_help reachable_top nintf_reflx
        SM.intro[of vpeq1 "scheduler sysconf" domain_of_event interference1]
        SM_enabled_axioms.intro [of s0t exec_event] 
        SM_enabled.intro[of domain_of_event "scheduler sysconf" vpeq1 interference1 s0t exec_event] by blast

subsection \<open>Some lemmas of security proofs\<close>

lemma sche_imp_not_part:
  "is_a_scheduler sysconf d \<Longrightarrow> \<not> (is_a_partition sysconf d)"      
  using sch_not_part by auto

lemma part_imp_not_sch:
  "is_a_partition sysconf d \<Longrightarrow> \<not> (is_a_scheduler sysconf d)"
  by (auto simp add: sch_not_part)

subsection \<open>proving "allocate memory" satisfying the "local respect" property\<close>
lemma alloc_memory_notchg_current:
  "\<lbrakk>is_a_partition sysconf (current s);
  s' = alloc_memory sysconf s po lv\<rbrakk>
  \<Longrightarrow> current s = current s'"
  by(clarsimp simp: alloc_memory_def get_partconf_byid_def get_partmem_byid_def Let_def)

lemma alloc_memory_sm_sche:
  "\<lbrakk>is_a_partition sysconf (current s);
  s' = alloc_memory sysconf s po lv\<rbrakk>
  \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
  using alloc_memory_notchg_current part_imp_not_sch
  by(meson vpeq1_def vpeq_sched_def)

lemma alloc_memory_notchg_partstate:
  "\<lbrakk>is_a_partition sysconf (current s);
  is_a_partition sysconf d;
  d \<noteq> current s;
  s' = alloc_memory sysconf s po lv\<rbrakk>
  \<Longrightarrow> (partitionmem s) d = (partitionmem s') d"
  by(clarsimp simp: alloc_memory_def get_partconf_byid_def get_partmem_byid_def Let_def)

lemma alloc_memory_sm_nitfpart:
  "\<lbrakk>reachable0 s;
  is_a_partition sysconf (current s);
  is_a_partition sysconf d;
  ((current s) \<setminus>\<leadsto> d);
  s' = alloc_memory sysconf s po lv\<rbrakk>
  \<Longrightarrow> (s \<sim> d \<sim> s')"
  using sche_imp_not_part 
  apply(clarsimp cong del: is_a_partition_def interference1_def non_interference1_def)
  using nintf_neq alloc_memory_notchg_partstate by blast

lemma alloc_memory_presrv_lcrsp:
  assumes p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p2:"(current s) \<setminus>\<leadsto> d"
    and   p3:"s' = alloc_memory sysconf s po lv"
  shows   "s \<sim> d \<sim> s'"
proof(cases "is_a_scheduler sysconf d")
  assume a0:"is_a_scheduler sysconf d"
  then show ?thesis using is_a_scheduler_def alloc_memory_sm_sche[OF p1 p3] by auto
next
  assume a1:"\<not> is_a_scheduler sysconf d"
  show ?thesis
  proof(cases "is_a_partition sysconf d")
    assume b0:"is_a_partition sysconf d"
    show ?thesis using b0 alloc_memory_sm_nitfpart p0 p1 p2 p3 by blast
  next
    assume b1:"\<not> is_a_partition sysconf d"
    show ?thesis using a1 b1 by auto
  qed
qed

lemma alloc_memory_presrv_lcrsp_e:
  "local_respect_e (hyperc (Buddy_Memory_Alloc po lv))"
  using alloc_memory_presrv_lcrsp exec_event_def
        prod.simps(2) vpeq_reflexive_lemma
  by(auto cong del: vpeq1_def)

subsection \<open>proving "free memory" satisfying the "local respect" property\<close>
lemma free_memory_notchg_current:
  "\<lbrakk>is_a_partition sysconf (current s);
  s' = free_memory sysconf s po b lv\<rbrakk>
  \<Longrightarrow> current s = current s'"
  by(clarsimp simp: free_memory_def get_partconf_byid_def get_partmem_byid_def Let_def)

lemma free_memory_sm_sche:
  "\<lbrakk>is_a_partition sysconf (current s);
  s' = free_memory sysconf s po b lv\<rbrakk>
  \<Longrightarrow> (s\<sim>(scheduler sysconf)\<sim>s')"
  using free_memory_notchg_current part_imp_not_sch
  by(meson vpeq1_def vpeq_sched_def)

lemma free_memory_notchg_partstate:
  "\<lbrakk>is_a_partition sysconf (current s);
  is_a_partition sysconf d;
  d \<noteq> current s;
  s' = free_memory sysconf s po b lv\<rbrakk>
  \<Longrightarrow> (partitionmem s) d = (partitionmem s') d"
  by(clarsimp simp: free_memory_def get_partconf_byid_def get_partmem_byid_def Let_def)

lemma free_memory_sm_nitfpart:
  "\<lbrakk>reachable0 s;
  is_a_partition sysconf (current s);
  is_a_partition sysconf d;
  ((current s) \<setminus>\<leadsto> d);
  s' = free_memory sysconf s po b lv\<rbrakk>
  \<Longrightarrow> (s \<sim> d \<sim> s')"
  using sche_imp_not_part 
  apply(clarsimp cong del: is_a_partition_def interference1_def non_interference1_def)
  using nintf_neq free_memory_notchg_partstate by blast

lemma free_memory_presrv_lcrsp:
  assumes p0:"reachable0 s"
    and   p1:"is_a_partition sysconf (current s)"
    and   p2:"(current s) \<setminus>\<leadsto> d"
    and   p3:"s' = free_memory sysconf s po b lv"
  shows   "s \<sim> d \<sim> s'"
proof(cases "is_a_scheduler sysconf d")
  assume a0:"is_a_scheduler sysconf d"
  then show ?thesis using is_a_scheduler_def free_memory_sm_sche[OF p1 p3] by auto
next
  assume a1:"\<not> is_a_scheduler sysconf d"
  show ?thesis
  proof(cases "is_a_partition sysconf d")
    assume b0:"is_a_partition sysconf d"
    show ?thesis using b0 free_memory_sm_nitfpart p0 p1 p2 p3 by blast
  next
    assume b1:"\<not> is_a_partition sysconf d"
    show ?thesis using a1 b1 by auto
  qed
qed

lemma free_memory_presrv_lcrsp_e:
  "local_respect_e (hyperc (Buddy_Memory_Free po b lv))"
  using free_memory_presrv_lcrsp exec_event_def
        prod.simps(2) vpeq_reflexive_lemma
  by(auto cong del: vpeq1_def)

subsection \<open>proving "schedule" satisfying the "local respect" property\<close>
lemma schedule_presrv_lcrsp:
  assumes p0:"(scheduler sysconf) \<setminus>\<leadsto> d"        
  shows   "s \<sim> d \<sim> s'"
  using p0 by auto

lemma schedule_presrv_lcrsp_e: "local_respect_e (sys Schedule)"
  using schedule_presrv_lcrsp exec_event_def prod.simps(2) vpeq_reflexive_lemma by auto

subsection \<open>proving the "local respect" property\<close>
theorem local_respect:local_respect
  proof -
    {
      fix e
      have "local_respect_e e"
        apply(induct e)
        using alloc_memory_presrv_lcrsp_e free_memory_presrv_lcrsp_e
        apply (rule Hypercall.induct)
        using schedule_presrv_lcrsp_e
        by (rule System_Event.induct)
    }
    then show ?thesis using local_respect_all_evt by blast
  qed

subsection \<open>proving "allocate memory" satisfying the "step consistent" property\<close>
lemma alloc_memory_presrv_wk_stp_cons:
      assumes p1:"is_a_partition sysconf (current s)"
        and   p2:"reachable0 s \<and> reachable0 t"
        and   p3:"s \<sim> d \<sim> t"
        and   p4:"s \<sim> (scheduler sysconf) \<sim> t"
        and   p5:"(current s) \<leadsto> d"
        and   p6:"s \<sim> (current s) \<sim> t"
        and   p7:"s' = alloc_memory sysconf s po lv"
        and   p8:"t' = alloc_memory sysconf t po lv"
      shows   "s' \<sim> d \<sim> t'"
proof(cases "is_a_scheduler sysconf d")
  assume a0:"is_a_scheduler sysconf d"
  show ?thesis by (smt a0 interference1_def p1 p5 sche_imp_not_part)
next
  assume a1:"\<not> is_a_scheduler sysconf d"
  show ?thesis
  proof(cases "is_a_partition sysconf d")
    assume b0:"is_a_partition sysconf d"
    show ?thesis
    proof(cases "current s = d")
      assume c0:"current s = d"
      have d0:"vpeq_part s' d t'"
      proof-
        {
          have e1:"partitionmem s' d = partitionmem t' d"
          proof-
            {
              from p3 b0 have f1:"partitionmem s d = partitionmem t d" 
                using a1 by fastforce
              from p7 have f2: "the (partitionmem s' d) = the (partitionmem s d) + {#lv#}"
                unfolding alloc_memory_def apply simp
              have "partitionmem s' d = partitionmem t' d" sorry
            }
            then show ?thesis by auto
          qed
          then have "vpeq_part s' d t'" using vpeq_part_def by auto
        }
        then show ?thesis by auto
      qed
      then show ?thesis using a1 b0 c0 by fastforce
    next
      assume c1:"current s \<noteq> d"
      have d1:"vpeq_part s' d t'"
      proof-
        {
          have e1:"partitionmem s' d = partitionmem t' d"
            using alloc_memory_notchg_partstate
            by (meson c1 interference1_def p1 p5 sche_imp_not_part)
          then have "vpeq_part s' d t'" using vpeq_part_def by auto
        }
        then show ?thesis by auto
      qed
      then show ?thesis using a1 b0 c1 by auto
    qed
  next
    assume b1:"\<not> is_a_partition sysconf d"
    show ?thesis using a1 b1 by auto
  qed
qed

lemma alloc_memory_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Buddy_Memory_Alloc po lv))"
  using alloc_memory_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
        non_interference_def singletonD sched_vpeq
  sorry
 (* by (smt Event.case(1) Hypercall.case(1) domain_of_event.simps(1) event_enabled.simps(1) option.sel prod.simps(2))*)

subsection \<open>proving "free memory" satisfying the "step consistent" property\<close>
lemma free_memory_presrv_wk_stp_cons_e: "weak_step_consistent_e (hyperc (Buddy_Memory_Free po b lv))"
  sorry

subsection \<open>proving "schedule" satisfying the "step consistent" property\<close>
lemma schedule_presrv_wk_stp_cons:
    assumes p1:"reachable0 s \<and> reachable0 t"
      and   p3:"s \<sim> d \<sim> t"
      and   p5:"(scheduler sysconf) \<leadsto> d"
      and   p6:"s \<sim> (scheduler sysconf) \<sim> t"
      and   p7:"s' \<in> schedule sysconf s"
      and   p8:"t' \<in> schedule sysconf t"
    shows   "s' \<sim> d \<sim> t'"
proof(cases "is_a_scheduler sysconf d")
  assume a0: "is_a_scheduler sysconf d"
  from p7 p8 have "current s' = current t'" unfolding schedule_def by simp
  with a0 show ?thesis using a0 p3 p7 p8 schedule_def by auto 
next
  assume a1: "\<not> is_a_scheduler sysconf d"
  show ?thesis
  proof(cases "is_a_partition sysconf d")
    assume b0: "is_a_partition sysconf d"
    with p3 have b00: "vpeq_part s d t"
      unfolding vpeq1_def by (metis a1 is_a_scheduler_def)
    have b1: "vpeq_part s' d t'"
    proof -
      have c1:"partitionmem s' d = partitionmem t' d"
      proof - 
        {
          from p3 b0 have f1:"partitionmem s d = partitionmem t d" 
            using a1 by fastforce
          from p7 have f2:"partitionmem s d = partitionmem s' d"
            by (simp add: schedule_def)
          from p8 have f3:"partitionmem t d = partitionmem t' d"
            by (simp add: schedule_def)
          with f1 f2 have "partitionmem s' d = partitionmem t' d" by auto
        }
        then show ?thesis by auto
      qed
      then have "vpeq_part s' d t'" using vpeq_part_def by simp
      then show ?thesis by auto
    qed
    then show ?thesis using a1 b0 by auto
  next
    assume b1: "\<not> is_a_partition sysconf d"
    show ?thesis using p3 p7 p8 schedule_def a1 b1 by auto         
  qed
qed

lemma schedule_presrv_wk_stp_cons_e: "weak_step_consistent_e (sys Schedule)"
  using schedule_presrv_wk_stp_cons weak_step_consistent_e_def exec_event_def mem_Collect_eq
        non_interference1_def non_interference_def singletonD sched_vpeq
  by (smt Event.case(2) System_Event.case(1) domain_of_event.simps(2) event_enabled.simps(2)
          option.sel prod.simps(2) vpeq1_def vpeq_sched_def)

subsection \<open>proving the "weakly step consistent" property\<close>
theorem weak_step_consistent:weak_step_consistent
  proof -
    {
      fix e
      have "weak_step_consistent_e e"
        apply(induct e)
        using alloc_memory_presrv_wk_stp_cons_e free_memory_presrv_wk_stp_cons_e
        apply (rule Hypercall.induct)
        using schedule_presrv_wk_stp_cons_e
        by (rule System_Event.induct)
    }
    then show ?thesis using weak_step_consistent_all_evt by blast
  qed

subsection \<open>Security Proofs\<close>

theorem noninfluence_sat: noninfluence
  using local_respect uc_eq_noninf weak_step_consistent weak_with_step_cons by blast

theorem noninfluence_gen_sat: noninfluence_gen
  using noninf_eq_noninf_gen noninfluence_sat by blast 

theorem weak_noninfluence_sat: weak_noninfluence
  using noninf_impl_weak noninfluence_sat by blast
  
theorem nonleakage_sat: nonleakage
  using noninf_impl_nonlk noninfluence_sat by blast

theorem noninterference_r_sat: noninterference_r
  using noninf_impl_nonintf_r noninfluence_sat by blast
  
theorem noninterference_sat: noninterference
  using noninterference_r_sat nonintf_r_impl_noninterf by blast
  
theorem weak_noninterference_r_sat: weak_noninterference_r
  using noninterference_r_sat nonintf_r_impl_wk_nonintf_r by blast
  
theorem weak_noninterference_sat: weak_noninterference
  using noninterference_sat nonintf_impl_weak by blast

end