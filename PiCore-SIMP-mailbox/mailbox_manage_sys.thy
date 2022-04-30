theory mailbox_manage_sys
imports rg_cond_post func_cor_other  func_cor_OSMboxAccept  func_cor_OSMboxPost
begin

definition OSMboxPost_RGF :: "Thread \<Rightarrow> mailbox_ref \<Rightarrow> Message option \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_e"
where "OSMboxPost_RGF t pevent msg  \<equiv> (OSMboxPost t pevent msg, OSMboxPost_RGCond t)"

definition OSMboxAccept_RGF :: "Thread \<Rightarrow> mailbox_ref \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_e"
 where "OSMboxAccept_RGF t pevent \<equiv> (OSMboxAccept t pevent, OSMboxAccept_RGCond t)"

definition Schedule_RGF :: "Thread \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_e"
where "Schedule_RGF t \<equiv> (Schedule t, Schedule_RGCond t)"

definition Tick_RGF :: "(EventLabel, Core, State, State com option) rgformula_e"
where "Tick_RGF \<equiv> (Tick, Tick_RGCond)"

definition Thread_RGF :: "Thread \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_es"
where "Thread_RGF t \<equiv>  (rgf_EvtSys ((\<Union>(pevent, msg).{OSMboxPost_RGF t pevent msg}) \<union>
                         (\<Union>(pevent). {OSMboxAccept_RGF t pevent})),
         RG[(OSMboxPost_pre t \<inter> OSMboxAccept_pre t \<inter> OSMboxPend_pre t),
            (OSMboxPost_rely t \<inter> OSMboxAccept_rely t \<inter> OSMboxPend_rely t ),
            (OSMboxPost_guar t \<union> OSMboxAccept_guar t \<union> OSMboxPend_guar t),
            (OSMboxPost_post t \<union> OSMboxAccept_post t \<union> OSMboxPend_post t )
           ])"

definition Scheduler_RGF :: "(EventLabel, Core, State, State com option) rgformula_es"
where "Scheduler_RGF \<equiv>  (rgf_EvtSys (\<Union>t. {Schedule_RGF t}),
         RG[{s. inv s}, Schedule_rely, Schedule_guar, {s. inv s}])"

definition Timer_RGF :: "(EventLabel, Core, State, State com option) rgformula_es"
where "Timer_RGF \<equiv>  (rgf_EvtSys {Tick_RGF},
         RG[\<lbrace>True\<rbrace>, Tick_rely, Tick_guar, \<lbrace>True\<rbrace>])"

definition Mailbox_manage_system_Spec :: "(EventLabel, Core, State, State com option) rgformula_par"
where "Mailbox_manage_system_Spec k \<equiv> 
    case k of (\<T> t) \<Rightarrow> Thread_RGF t
            | \<S> \<Rightarrow> Scheduler_RGF
            | Timer \<Rightarrow> Timer_RGF"


section \<open> functional correctness of the whole specification\<close>
definition "sys_rely \<equiv> {}"
(*definition "sys_rely \<equiv> {(s,t). inv s \<longrightarrow> inv t}"*)
(*definition "sys_rely \<equiv> (\<Inter>t. lvars_nochange_rel t) \<inter> gvars_conf_stable \<inter> {(s,t). inv s \<longrightarrow> inv t}"*)

definition "sys_guar \<equiv> Tick_guar \<union> Schedule_guar \<union> (\<Union>t. (OSMboxPost_guar t \<union> OSMboxAccept_guar t \<union> OSMboxPend_guar t ))"

lemma scheduler_esys_sat: "\<Gamma> \<turnstile> fst (Mailbox_manage_system_Spec \<S>) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Mailbox_manage_system_Spec \<S>), 
        Rely\<^sub>e\<^sub>s (Mailbox_manage_system_Spec \<S>), 
        Guar\<^sub>e\<^sub>s (Mailbox_manage_system_Spec \<S>), 
        Post\<^sub>e\<^sub>s (Mailbox_manage_system_Spec \<S>)]"
apply(simp add:Mailbox_manage_system_Spec_def Scheduler_RGF_def Schedule_RGF_def)
  apply(rule EvtSys_h)
    apply auto[1] apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def)
    using Schedule_satRG apply(simp add:Schedule_RGCond_def Evt_sat_RG_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def)
    apply fast
    apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def Schedule_RGCond_def getrgformula_def) 
    apply(simp add:Pre\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)
      using stable_inv_sched_rely apply(simp add:stable_def)
    apply(simp add:Guar\<^sub>e\<^sub>s_def getrgformula_def Schedule_guar_def) 
      done


lemma Post_rely_eq_Accept_rely:"OSMboxPost_rely x  = OSMboxAccept_rely x "
  apply(simp add:OSMboxPost_rely_def OSMboxAccept_rely_def)
  done


lemma temp:"OSMboxPost_rely x \<inter> OSMboxAccept_rely x = OSMboxPost_rely x"
  apply (simp add:OSMboxPost_rely_def OSMboxAccept_rely_def)
  done


lemma thread_esys_sat: "\<Gamma> \<turnstile> fst (Mailbox_manage_system_Spec (\<T> x)) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Mailbox_manage_system_Spec (\<T> x)), 
        Rely\<^sub>e\<^sub>s (Mailbox_manage_system_Spec (\<T> x)), 
        Guar\<^sub>e\<^sub>s (Mailbox_manage_system_Spec (\<T> x)), 
        Post\<^sub>e\<^sub>s (Mailbox_manage_system_Spec (\<T> x))]"
apply(simp add:Mailbox_manage_system_Spec_def Thread_RGF_def OSMboxPost_RGF_def OSMboxAccept_RGF_def)
apply(rule EvtSys_h)
  apply auto[1] 
    apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
      using OSMboxPost_satRG apply(simp add:Evt_sat_RG_def OSMboxPost_RGCond_def 
                                      getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def) apply fast
    apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
      using OSMboxAccept_satRG apply(simp add:Evt_sat_RG_def OSMboxAccept_RGCond_def 
                                      getrgformula_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def) apply fast
  apply auto[1]
    apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
    apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
  apply auto[1]
    apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
    apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
  apply auto[1]
    apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
    apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
  apply auto[1]
    apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def) 
    apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
  apply auto[1]
           apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def OSMboxPost_RGCond_def getrgformula_def OSMboxPost_post_def)apply auto
      apply(simp add:inv_def OSMboxPost_pre_def)
    apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def OSMboxPost_RGCond_def OSMboxAccept_RGCond_def 
          getrgformula_def OSMboxPost_post_def)
 apply(simp add:inv_def OSMboxAccept_pre_def)
    apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def OSMboxPost_RGCond_def OSMboxAccept_RGCond_def 
          getrgformula_def OSMboxAccept_post_def)
         apply(simp add:inv_def OSMboxPost_pre_def)
        apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def OSMboxAccept_RGCond_def getrgformula_def OSMboxAccept_post_def)
 apply(simp add:inv_def OSMboxAccept_pre_def)
  apply(simp add:Pre\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def) 
    defer 1 (* proved in mem_alloc *)
       apply(simp add:Guar\<^sub>e\<^sub>s_def getrgformula_def OSMboxAccept_guar_def) 

      apply(simp add:OSMboxAccept_pre_def OSMboxPost_pre_def OSMboxPend_pre_def)
      apply(simp add:temp)
      apply(simp add:inv_def OSMboxPost_rely_def inv_cur_def stable_def OSMboxPend_rely_def)
      done



lemma timer_esys_sat: "\<Gamma> \<turnstile> fst (Mailbox_manage_system_Spec Timer) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Mailbox_manage_system_Spec Timer), 
        Rely\<^sub>e\<^sub>s (Mailbox_manage_system_Spec Timer), 
        Guar\<^sub>e\<^sub>s (Mailbox_manage_system_Spec Timer), 
        Post\<^sub>e\<^sub>s (Mailbox_manage_system_Spec Timer)]"
apply(simp add:Mailbox_manage_system_Spec_def Timer_RGF_def Tick_RGF_def)
apply(rule EvtSys_h)
  apply auto[1] apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def)
    using Tick_satRG apply(simp add:Tick_RGCond_def Evt_sat_RG_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def) 
    apply fast
  apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def Tick_RGCond_def)
  apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def Tick_RGCond_def)
  apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def Tick_RGCond_def)
  apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def Tick_RGCond_def)
  apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def Tick_RGCond_def getrgformula_def) 
  apply(simp add:Pre\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)
    using stable_inv_sched_rely apply(simp add:stable_def)
  apply(simp add:Guar\<^sub>e\<^sub>s_def getrgformula_def Tick_guar_def) 
done

lemma esys_sat: "\<Gamma> \<turnstile> fst (Mailbox_manage_system_Spec k) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k), 
        Rely\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k), 
        Guar\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k), 
        Post\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k)]"
  apply(induct k)
  using scheduler_esys_sat apply fast 
  using thread_esys_sat apply fast
  using timer_esys_sat apply fast
done

lemma s0_esys_pre: "{s0} \<subseteq> Pre\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k)"
apply(induct k)
  apply(simp add:Mailbox_manage_system_Spec_def Pre\<^sub>e\<^sub>s_def Scheduler_RGF_def getrgformula_def)    (*System 1: Scheduler *)
  using s0_inv apply fast

     apply(simp add:Mailbox_manage_system_Spec_def Pre\<^sub>e\<^sub>s_def Thread_RGF_def getrgformula_def)    (*System 2: Thread *)
    using s0_inv s0a4 s0a1 s0a2 s0a3 apply auto[1]
      apply(simp add:inv_def OSMboxPost_pre_def)
      apply(simp add:inv_def OSMboxAccept_pre_def)
     apply(simp add:inv_def OSMboxPend_pre_def)

  apply(simp add:Mailbox_manage_system_Spec_def Pre\<^sub>e\<^sub>s_def Timer_RGF_def getrgformula_def)       (*System 3: Timer *)
done


lemma alloc_free_eq_guar: " OSMboxPost_guar x\<subseteq> OSMboxAccept_guar x "
  apply(simp add:OSMboxAccept_guar_def OSMboxPost_guar_def)
  apply(simp add:gvars_conf_stable_def)
  apply auto
         apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)apply auto


lemma alloc_free_eq_rely: "OSMboxAccept_rely x = OSMboxPost_rely x"
  by(simp add:OSMboxAccept_rely_def OSMboxPost_rely_def)

lemma esys_guar_in_other:
  "jj \<noteq> k \<longrightarrow> Guar\<^sub>e\<^sub>s (Mailbox_manage_system_Spec jj) \<subseteq> Rely\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k)"
  apply auto
  apply(induct jj)
    apply(induct k)
      apply simp
     apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Mailbox_manage_system_Spec_def Scheduler_RGF_def Thread_RGF_def getrgformula_def)
  using Schedguar_in_OSMemGetrely  apply(simp add:OSMboxPost_rely_def OSMboxAccept_rely_def) apply auto[1]
  apply(induct k)
  using OSMemGetguar_in_OSMemGetrely OSMem_eq_guar OSMem_eq_rely by fast+

thm esys_guar_in_other

lemma esys_guar_in_sys: "Guar\<^sub>e\<^sub>s (Mailbox_manage_system_Spec k) \<subseteq> sys_guar"
apply(induct k)
  apply(simp add:Guar\<^sub>e\<^sub>s_def Mailbox_manage_system_Spec_def Scheduler_RGF_def getrgformula_def sys_guar_def) apply auto[1]
  apply(simp add:Guar\<^sub>e\<^sub>s_def Mailbox_manage_system_Spec_def Thread_RGF_def getrgformula_def sys_guar_def) apply auto[1]
  apply(simp add:Guar\<^sub>e\<^sub>s_def Mailbox_manage_system_Spec_def Timer_RGF_def getrgformula_def sys_guar_def) apply auto[1]
done

lemma mailbox_sys_sat: "\<Gamma> \<turnstile> Mailbox_manage_system_Spec SAT [{s0}, sys_rely, sys_guar, UNIV]"
apply(rule ParallelESys[of \<Gamma> Mailbox_manage_system_Spec"{s0}" sys_rely sys_guar UNIV])
  apply clarify using esys_sat apply fast
  using s0_esys_pre apply fast
  apply(simp add:sys_rely_def)
  using esys_guar_in_other apply fast
  using esys_guar_in_sys apply fast
  apply simp
  done


end