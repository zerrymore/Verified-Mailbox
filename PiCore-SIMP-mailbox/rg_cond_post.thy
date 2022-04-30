theory rg_cond_post
imports mem_spec invariant (*"../picore-lib/picore_lemma"*)
begin

section \<open>Rely-guarantee condition of events\<close>

subsection \<open>defs of rely-guarantee conditions\<close>
definition lvars_nochange_lemma :: "Thread \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
where "lvars_nochange_lemma t r s \<equiv> 
    posting_msg r t = posting_msg s t (*  \<and> statPend r t = statPend s t  *)   (*IF not, OSMboxPost succeed, else Pend succeed) statpend and tmout  *)
    \<and> ret r t = ret s t \<and> endt r t = endt s t (* \<and> tmout r t = tmout s t *)
    \<and> th r t = th s t \<and> need_resched r t = need_resched s t "


definition lvars_nochange_lemma_rel :: "Thread \<Rightarrow> (State \<times> State) set"
where "lvars_nochange_lemma_rel t \<equiv> {(s,r). lvars_nochange_lemma t s r}"

definition lvars_nochange_lemma_4all :: "(State \<times> State) set"
  where "lvars_nochange_lemma_4all \<equiv> {(s,r). \<forall>t. lvars_nochange_lemma t s r}"



definition lvars_nochange :: "Thread \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
where "lvars_nochange t r s \<equiv> 
    posting_msg r t = posting_msg s t  \<and> statPend r t = statPend s t     (*IF not, OSMboxPost succeed, else Pend succeed) statpend and tmout  *)
    \<and> ret r t = ret s t \<and> endt r t = endt s t  \<and> tmout r t = tmout s t
    \<and> th r t = th s t \<and> need_resched r t = need_resched s t "


definition lvars_nochange_rel :: "Thread \<Rightarrow> (State \<times> State) set"
where "lvars_nochange_rel t \<equiv> {(s,r). lvars_nochange t s r}"

definition lvars_nochange_4all :: "(State \<times> State) set"
where "lvars_nochange_4all \<equiv> {(s,r). \<forall>t. lvars_nochange t s r}"




lemma lvars_nochange_lemma_trans:
"lvars_nochange_lemma t x y \<Longrightarrow> lvars_nochange_lemma t y z \<Longrightarrow> lvars_nochange_lemma t x z"
apply(simp add:lvars_nochange_lemma_def)
done

lemma lvars_nochange_lemma_sym:
"lvars_nochange_lemma t x y \<Longrightarrow> lvars_nochange_lemma t y x"
apply(simp add:lvars_nochange_lemma_def)
done

lemma lvars_nochange_lemma_refl:
"lvars_nochange_lemma t x x"
apply(simp add:lvars_nochange_lemma_def)
done


lemma lv_noch_all1: "(s,r)\<in>lvars_nochange_lemma_4all 
      \<Longrightarrow> (s,r)\<in>lvars_nochange_lemma_rel t \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> (s,r)\<in>lvars_nochange_lemma_rel t')"
  unfolding lvars_nochange_lemma_4all_def lvars_nochange_lemma_rel_def by auto

lemma lv_noch_all2: "(s,r)\<in>lvars_nochange_lemma_rel t \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange_lemma t' s r) 
        \<Longrightarrow> (s,r)\<in>lvars_nochange_lemma_4all"
  unfolding lvars_nochange_lemma_4all_def lvars_nochange_lemma_rel_def by auto


definition gvars_nochange :: "State \<Rightarrow> State \<Rightarrow> bool"
where "gvars_nochange s r \<equiv> cur r = cur s \<and> tick r = tick s \<and> thd_state r = thd_state s 
                          \<and> OSMailBoxs r = OSMailBoxs s \<and> OSMailbox_info r = OSMailbox_info s"

definition gvars_nochange_rel :: "(State \<times> State) set"
where "gvars_nochange_rel \<equiv> {(s,r). gvars_nochange s r}"


text\<open> the static configurations of struct Mail_Box unchange('buf' is the only static member of Mail_box) \<close>

definition gvars_conf :: "State \<Rightarrow> State \<Rightarrow> bool"
where "gvars_conf s r \<equiv> 
  OSMailBoxs r = OSMailBoxs s 
    \<and> (\<forall>p. buf (OSMailbox_info s p) = buf (OSMailbox_info r p))"


definition gvars_conf_stable :: "(State \<times> State) set"
where "gvars_conf_stable \<equiv> {(s,r). gvars_conf s r}"

definition inv_sta_rely :: "(State \<times> State) set"
where "inv_sta_rely \<equiv> {(s,r). inv s \<longrightarrow> inv r}"

definition inv_sta_guar :: "(State \<times> State) set"
where "inv_sta_guar \<equiv> {(s,r). inv s \<longrightarrow> inv r}"


lemma glnochange_inv0:
  "(a, b) \<in> lvars_nochange_lemma_4all \<Longrightarrow> cur a = cur b \<Longrightarrow>
     thd_state a = thd_state b \<Longrightarrow> OSMailBoxs a = OSMailBoxs b \<Longrightarrow>
     OSMailbox_info a = OSMailbox_info b \<Longrightarrow> inv a \<Longrightarrow> inv b"
  apply(simp add:lvars_nochange_lemma_4all_def lvars_nochange_lemma_def inv_def)
  apply(rule conjI) apply(simp add:inv_cur_def)
   apply(simp add:inv_thd_waitq_def) apply auto[1]
done


lemma glnochange_inv: 
  "inv a \<Longrightarrow> \<forall>t'. t' \<noteq> t1 \<longrightarrow> lvars_nochange_lemma t' a b 
      \<Longrightarrow> gvars_nochange a b \<Longrightarrow> lvars_nochange_lemma t1 a b \<Longrightarrow> inv b" 
  apply(subgoal_tac "(a, b) \<in> lvars_nochange_lemma_4all")
    apply(simp add: gvars_nochange_def)
    using glnochange_inv0 apply auto
  using lv_noch_all2[of a b t1] apply auto[1] 
  by(simp add: lvars_nochange_lemma_rel_def)


definition Schedule_rely :: "(State \<times> State) set"
where "Schedule_rely \<equiv> {(s,r). inv s \<longrightarrow> inv r} \<union> Id"


definition Schedule_guar :: "(State \<times> State) set"
where "Schedule_guar \<equiv> 
  ((*\<lbrace>(\<ordmasculine>cur \<noteq> Some t \<longrightarrow> 
          (\<ordmasculine>cur \<noteq> None \<longrightarrow> \<ordfeminine>thd_state = (\<ordmasculine>thd_state (the (\<ordmasculine>cur) := READY))(t := RUNNING) \<and> \<ordfeminine>cur = Some t)
        \<and> (\<ordmasculine>cur = None \<longrightarrow> \<ordfeminine>thd_state = \<ordmasculine>thd_state (t := RUNNING)) \<and> \<ordfeminine>cur = Some t)
    \<and> (\<ordmasculine>cur = Some t \<longrightarrow> \<ordfeminine>thd_state = \<ordmasculine>thd_state \<and> \<ordmasculine>cur = \<ordfeminine>cur) \<rbrace>*)
   {(s,r). inv s \<longrightarrow> inv r}
   \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick \<and> \<ordmasculine>OSMailBoxs = \<ordfeminine>OSMailBoxs \<and> \<ordmasculine>OSMailbox_info = \<ordfeminine>OSMailbox_info\<rbrace> 
   \<inter> (\<Inter>t. lvars_nochange_rel t)) \<union> Id"


definition Schedule_RGCond :: "Thread \<Rightarrow> (State) PiCore_Hoare.rgformula"
  where "Schedule_RGCond t \<equiv> 
          RG[{s. inv s},
          Schedule_rely,  Schedule_guar,
          {s. inv s}]"

definition Tick_rely :: "(State \<times> State) set"
where "Tick_rely \<equiv> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace> \<union> Id"

definition Tick_guar :: "(State \<times> State) set"
where "Tick_guar \<equiv> (\<lbrace>\<ordfeminine>tick = \<ordmasculine>tick + 1 \<and> \<ordmasculine>cur = \<ordfeminine>cur \<and> \<ordmasculine>thd_state = \<ordfeminine>thd_state
                      \<and> \<ordmasculine>OSMailBoxs = \<ordfeminine>OSMailBoxs \<and> \<ordmasculine>OSMailbox_info = \<ordfeminine>OSMailbox_info\<rbrace>
                      \<inter> (\<Inter>t. lvars_nochange_rel t)) \<union> Id"

definition Tick_RGCond :: "(State) PiCore_Hoare.rgformula"
  where "Tick_RGCond \<equiv> 
          RG[\<lbrace>True\<rbrace>, Tick_rely, Tick_guar, \<lbrace>True\<rbrace>]"


definition OSMboxPost_pre :: "Thread \<Rightarrow> State set"
where "OSMboxPost_pre t \<equiv> {s. inv s}"

definition OSMboxPost_rely_lemma :: "Thread \<Rightarrow> (State \<times> State) set"
where "OSMboxPost_rely_lemma t \<equiv> 
   ((lvars_nochange_lemma_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange_lemma t' s r))}) \<union> Id)"     \<comment> \<open>The rely condition of Mem_alloc is the same as one of Mem_free \<close>

definition OSMboxPost_guar :: "Thread \<Rightarrow> (State \<times> State) set"  
where "OSMboxPost_guar t \<equiv> 
        ((gvars_conf_stable \<inter> 
          {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange_lemma t s r)
                  \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r) 
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange_lemma t' s r) }
          \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)"


definition OSMboxPost_post :: "Thread \<Rightarrow> State set"
where "OSMboxPost_post t \<equiv> {s. inv s}"

definition OSMboxPost_RGCond_lemma :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxPost_RGCond_lemma t  \<equiv> 
          RG[OSMboxPost_pre t,
             OSMboxPost_rely_lemma t,
              OSMboxPost_guar t,
              OSMboxPost_post t]"


definition OSMboxPost_rely :: "Thread \<Rightarrow> (State \<times> State) set"
where "OSMboxPost_rely t \<equiv> 
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)"     \<comment> \<open>The rely condition of Mem_alloc is the same as one of Mem_free \<close>


definition OSMboxPost_RGCond :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxPost_RGCond t  \<equiv> 
          RG[OSMboxPost_pre t,
             OSMboxPost_rely t,
              OSMboxPost_guar t,
              OSMboxPost_post t]"


definition OSMboxAccept_pre :: "Thread \<Rightarrow> State set"
  where "OSMboxAccept_pre t \<equiv> {s. inv s}"

definition OSMboxAccept_rely :: "Thread \<Rightarrow> (State \<times> State) set"

where "OSMboxAccept_rely t \<equiv> 
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)"     \<comment> \<open>The rely condition of Mem_alloc is the same as one of Mem_free \<close>

definition OSMboxAccept_guar :: "Thread \<Rightarrow> (State \<times> State) set"  
where "OSMboxAccept_guar t \<equiv> 
        ((gvars_conf_stable \<inter> 
          {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
                  \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r) 
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r) }
          \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)"


definition OSMboxAccept_post :: "Thread \<Rightarrow> State set"
where "OSMboxAccept_post t \<equiv> {s. inv s}"


definition OSMboxAccept_RGCond :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxAccept_RGCond t  \<equiv> 
          RG[OSMboxAccept_pre t,
             OSMboxAccept_rely t,
              OSMboxAccept_guar t,
              OSMboxAccept_post t]"




definition OSMboxPend_pre :: "Thread \<Rightarrow> State set"
where "OSMboxPend_pre t \<equiv> {s. inv s }"

definition OSMboxPend_rely :: "Thread \<Rightarrow> (State \<times> State) set"
where "OSMboxPend_rely t \<equiv> 
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)"


definition OSMboxPend_guar :: "Thread \<Rightarrow> (State \<times> State) set"
where "OSMboxPend_guar t \<equiv> 
        ((gvars_conf_stable \<inter> 
          {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
                  \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r) 
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r) }
          \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)"

definition OSMboxPend_post :: "Thread \<Rightarrow> State set"
where "OSMboxPend_post t \<equiv> {s. inv s }"



definition OSMboxPend_RGCond :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxPend_RGCond t  \<equiv> 
          RG[OSMboxPend_pre t,
             OSMboxPend_rely t,
              OSMboxPend_guar t,
              OSMboxPend_post t]"



subsection \<open>stablility, subset relations of rely-guarantee conditions\<close>


lemma stable_inv_Post_rely:
  "(s,r) \<in> OSMboxPost_rely t \<Longrightarrow> inv s \<Longrightarrow> inv r"
  using OSMboxPost_rely_def by blast

lemma stable_inv_Post_rely1: "stable \<lbrace> \<acute>inv \<rbrace> (OSMboxPost_rely t)"
  using stable_inv_Post_rely unfolding stable_def by auto

lemma stable_inv_Accept_rely:
  "(s,r) \<in> OSMboxAccept_rely t \<Longrightarrow> inv s \<Longrightarrow> inv r"
  using OSMboxAccept_rely_def by blast

lemma stable_inv_Accept_rely1: "stable \<lbrace> \<acute>inv \<rbrace> (OSMboxAccept_rely t)"
  by (simp add: stable_def stable_inv_Accept_rely)



lemma stable_inv_sched_rely:
  "(s,r)\<in>Schedule_rely \<Longrightarrow> inv s \<Longrightarrow> inv r"
  apply (simp add:Schedule_rely_def) by auto

lemma stable_inv_sched_rely1: "stable \<lbrace>\<acute>inv\<rbrace> Schedule_rely"
  using stable_inv_sched_rely unfolding stable_def by auto

lemma sched_guar_stb_inv: 
  "(s,r)\<in>Schedule_guar \<Longrightarrow> inv s \<Longrightarrow> inv r"
  apply(simp add:Schedule_guar_def) 
  apply(erule disjE) by auto


lemma tick_guar_stb_inv:
"stable (Collect invariant.inv) Tick_guar"

lemma OSMboxPost_guar_stb_inv: "stable \<lbrace>\<acute>inv \<rbrace> (OSMboxPost_guar t)"  (* _lemma *)
proof-
  { 
    fix x
    assume a0: "inv x"
    {
      fix y 
      assume b0: "(x,y) \<in> OSMboxPost_guar t"
      hence "(x,y) \<in> {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
             \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r)
             \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r)}"
        using OSMboxPost_guar_def gvars_nochange_def lvars_nochange_def by auto
      hence "(cur x \<noteq> Some t \<longrightarrow> gvars_nochange x y \<and> lvars_nochange t x y)
              \<and> (cur x = Some t \<longrightarrow> inv x \<longrightarrow>inv y)
              \<and> (\<forall>t' . t' \<noteq> t \<longrightarrow> lvars_nochange t' x y)" by simp
      hence "inv y"
        apply(case_tac "cur x \<noteq> Some t")
         apply (simp add: gvars_nochange_def lvars_nochange_def) using a0 apply clarify
         apply(simp add:inv_def)
         apply (rule conjI) apply(simp add:inv_cur_def)
        using a0 by auto
    }
  }
  then show ?thesis by (simp add:stable_def)
qed

lemma Post_guar_eq_Accept_guar:"OSMboxAccept_guar t \<subseteq> OSMboxPost_guar t"
  apply (simp add: OSMboxAccept_guar_def OSMboxPost_guar_def)
  apply auto
                 apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
                apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
               apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
              apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
             apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
            apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
           apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
  apply(simp add: lvars_nochange_def lvars_nochange_lemma_def gvars_conf_stable_def gvars_conf_def)
  done        



lemma OSMboxAccept_guar_stb_inv: "stable \<lbrace> \<acute>inv \<rbrace> (OSMboxAccept_guar t)"
proof-
  { 
    fix x
    assume a0: "inv x"
    {
      fix y 
      assume b0: "(x,y) \<in> OSMboxPost_guar t"
      hence "(x,y) \<in> {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
             \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r)
             \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r)}"
        using OSMboxPost_guar_def gvars_nochange_def lvars_nochange_def by auto
      hence "(cur x \<noteq> Some t \<longrightarrow> gvars_nochange x y \<and> lvars_nochange t x y)
              \<and> (cur x = Some t \<longrightarrow> inv x \<longrightarrow>inv y)
              \<and> (\<forall>t' . t' \<noteq> t \<longrightarrow> lvars_nochange t' x y)" by simp
      hence "inv y"
        apply(case_tac "cur x \<noteq> Some t")
         apply (simp add: gvars_nochange_def lvars_nochange_def) using a0 apply clarify
         apply(simp add:inv_def)
         apply (rule conjI) apply(simp add:inv_cur_def)
        using a0 by auto
    }
  }
  then show ?thesis by (simp add:stable_def)
qed


lemma OSMboxPend_guar_stb_inv:"stable \<lbrace>\<acute>inv \<rbrace> (OSMboxPend_guar t) "
  apply(subgoal_tac " OSMboxPend_guar t = OSMboxAccept_guar t ")
  apply(simp add:OSMboxAccept_guar_stb_inv)
  by (simp add: OSMboxAccept_guar_def OSMboxPend_guar_def) 



lemma OSMboxAccept_pre_stb: "stable (OSMboxAccept_pre t) (OSMboxAccept_rely t)"
  by (simp add: OSMboxAccept_pre_def stable_inv_Accept_rely1)
                                              
lemma OSMboxAccept_post_stb: "stable (OSMboxPost_post t) (OSMboxPost_rely t)"
  by (simp add: OSMboxPost_post_def stable_inv_Post_rely1)

lemma OSMboxPost_pre_stb: "stable (OSMboxPost_pre t) (OSMboxPost_rely t)"
  by (simp add: OSMboxPost_pre_def stable_inv_Post_rely1)

lemma OSMboxPost_post_stb: "stable (OSMboxPost_pre t) (OSMboxPost_rely t)"
  by (simp add: OSMboxPost_pre_stb)









end