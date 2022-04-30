theory func_cor_OSMboxPost
  imports rg_cond_post
begin
thm OSMboxPost_def



lemma OSMboxPost_pre_stable:" stable (OSMboxPost_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>) (OSMboxPost_rely_lemma t) "
  by(simp add:OSMboxPost_pre_def OSMboxPost_rely_lemma_def stable_def gvars_conf_stable_def gvars_conf_def)


lemma OSMboxPost_post_stable:" stable (OSMboxPost_post t) (OSMboxPost_rely_lemma t) "
  by(simp add:OSMboxPost_post_def OSMboxPost_rely_lemma_def stable_def)

lemma mylist_nhd_in_tl: "dist_list l \<Longrightarrow> hd l \<notin> set (tl l) "
  by (meson dist_hd_nin_tl distinct_conv_nth)

lemma mylist_hd_in_list: "l \<noteq> [] \<Longrightarrow>hd l \<in> set l"
  by auto


text \<open>
we define inv_thd_waitq4 to represent the state where the hd of the waitq list  was removed from the waitq list
and the state of the hd(waitq) is still blocked.This lemma aims to show that inv_thd_waitq_mid4 V' can be derived from
the inv_thd_waitq V. V' = V\<lparr>wait_q = tl waitq\<rparr>.
\<close>
lemma inv_waitq_to_inv_waitq4: " \<And> V . pe \<in> OSMailBoxs V \<Longrightarrow> inv_thd_waitq V \<Longrightarrow> t = hd(wait_q (OSMailbox_info V pe)) \<Longrightarrow> (wait_q (OSMailbox_info V pe)) \<noteq> [] \<Longrightarrow>  
                 inv_thd_waitq_mid4  (V\<lparr>OSMailbox_info := (OSMailbox_info V) (pe :=OSMailbox_info V pe\<lparr>wait_q := tl (wait_q ((OSMailbox_info  V) pe))\<rparr>)\<rparr>) t "
  apply(simp add:OSMboxPost_pre_def inv_thd_waitq_def inv_thd_waitq_mid4_def)
  apply auto
        apply (metis list_nhd_in_tl_set)
       apply (simp add: mylist_nhd_in_tl)
  using mylist_hd_in_list apply blast
  apply (meson list.set_sel(2))
    apply (simp add: List.nth_tl less_diff_conv)
   apply (metis list.set_sel(2))
  by (meson list.set_sel(2))              \<comment> \<open>lemma test simulate the key step which transform the pre "inv_thd_waitq" to "inv_thd_waitq4"  \<close>



lemma myconj1: "A \<Longrightarrow> B  \<Longrightarrow> B"
  unfolding and_def by (iprover intro: impI [THEN allI] mp)  \<comment> \<open>the rule to remove the useless assumption \<close>


lemma inv_waitq5_to_inv_waitq:"\<And>t tx s. inv_thd_waitq_mid5 s tx \<Longrightarrow> inv_cur s \<Longrightarrow>  inv s"
  apply(simp add:inv_thd_waitq_mid5_def inv_thd_waitq_def inv_def inv_cur_def)apply auto
  by (metis Thread_State_Type.distinct(3))




text \<open>This lemma was proved to show that V' satifies: inv_thd_waitq_midx V' = True \<close>
lemma inv_waitq_to_inv_waitqx:"                    \<comment> \<open> to show that  V' satifies: inv_thd_waitq_midx V'\<close>
pevent \<in> OSMailBoxs V \<Longrightarrow>  inv_cur V \<Longrightarrow>  cur V = Some t \<Longrightarrow> inv_thd_waitq V  
 \<Longrightarrow> wait_q (OSMailbox_info V pevent) \<noteq> [] \<Longrightarrow>
let V2 =  
  V \<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
       get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
       OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
       need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
       thd_state := (thd_state V)
         (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
          SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
       ret := (ret V)(t := OK)\<rparr>
  in
 inv_thd_waitq_midx V2 (hd(wait_q (OSMailbox_info V pevent)))
"
  apply(subgoal_tac "inv_thd_waitq_midx V  (hd(wait_q (OSMailbox_info V pevent)))")
 apply(simp add:inv_thd_waitq_midx_def)apply auto 
            apply (metis list_nhd_in_tl_set)
           apply (simp add: mylist_nhd_in_tl)
           apply (metis Thread_State_Type.distinct(5) inv_cur_def  list.set_sel(2))

  apply (smt Thread_State_Type.distinct(3) list.set_sel(2) someI)
         apply (simp add: list.set_sel(2))
  using mylist_hd_in_list apply blast
       apply (metis Thread_State_Type.distinct(5) inv_cur_def)
      
      apply (smt Thread_State_Type.distinct(3) someI)
  apply (simp add: List.nth_tl Nitpick.size_list_simp(2))
  apply (meson list.set_sel(2))
  apply (meson list.set_sel(2))
  by (simp add: waitq_to_waitq_midx)



 (* without assumption "waitq V' \<noteq> []" , failed to prove this lemma  *)
lemma tet:" \<And>p.  
         inv_cur V \<Longrightarrow>
         cur V = Some t \<Longrightarrow> wait_q (OSMailbox_info V pevent) \<noteq> [] \<Longrightarrow> 
         \<forall>t. t \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> thd_state V t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs V. t \<in> set (wait_q (OSMailbox_info V p))) \<Longrightarrow>
         \<forall>p\<in>OSMailBoxs V. \<forall>t\<in>set (wait_q (OSMailbox_info V p)). thd_state V t = BLOCKED \<Longrightarrow>
         \<forall>p\<in>OSMailBoxs V. dist_list (wait_q (OSMailbox_info V p)) \<Longrightarrow>
          pevent \<in> OSMailBoxs V \<Longrightarrow>
         \<forall>p q. p \<in> OSMailBoxs V \<and> q \<in> OSMailBoxs V \<and> p \<noteq> q \<longrightarrow> (\<forall>t. t \<in> set (wait_q (OSMailbox_info V p)) \<longrightarrow> t \<notin> set (wait_q (OSMailbox_info V q))) \<Longrightarrow>
         p \<in> OSMailBoxs V \<Longrightarrow> p \<noteq> pevent \<Longrightarrow> hd (wait_q (OSMailbox_info V pevent)) \<in> set (wait_q (OSMailbox_info V p)) \<Longrightarrow> False "
  using mylist_hd_in_list by blast
 

text \<open> inv_thd_waitq_mid5 can be divided into two parts: 1. inv_thd_waitq_midx 2.thd_state V t = READY,
       i.e., inv_thd_waitq_mid5 = inv_thd_waitq_midx \<and> thd_state V t\<close>
lemma waitq_midx_and_Ready_eq_waitq5:"inv_thd_waitq_midx V t \<Longrightarrow> thd_state V t = READY \<Longrightarrow>inv_thd_waitq_mid5 V t "
  using inv_thd_waitq_mid5_def inv_thd_waitq_midx_def by auto
  

text \<open> this lemma is to show: (V,V')\<in>OSMboxPost_guar t \<close>
lemma VV'_in_OSMboxPost_guar:" msg = Some y \<Longrightarrow>
    pevent \<in> OSMailBoxs V \<Longrightarrow>
    invariant.inv V \<Longrightarrow>
    cur V = Some t \<Longrightarrow>
    wait_q (OSMailbox_info V pevent) \<noteq> [] \<Longrightarrow>
    (V, V
     \<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
        get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
        OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
        need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
        thd_state := (thd_state V)
          (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
           SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
        ret := (ret V)(t := OK)\<rparr>)
    \<in> OSMboxPost_guar t "
  apply(simp add:OSMboxPost_guar_def)
  apply auto
    apply(simp add:gvars_conf_stable_def gvars_conf_def)   (*prove:(V, V')\<in> gvars_conf_stable *)
  

   prefer 2
   apply(simp add:lvars_nochange_lemma_def) (*prove:\<forall>t'\<noteq>t. lvars_nochage t' V V' *)

\<comment> \<open>Next, we want to show that  V' satifies: inv V'\<close>
  apply(simp add:inv_def)
  apply(rule conjI)
apply(simp add:inv_cur_def)
   apply auto[1]
  apply(subgoal_tac "let Vx =  V
       \<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
       get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
       OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
       need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
       thd_state := (thd_state V)
         (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
          SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
       ret := (ret V)(t := OK)\<rparr> in
                     inv_thd_waitq_mid5 Vx (hd(wait_q (OSMailbox_info V pevent)))")

  apply(simp add:inv_thd_waitq_mid5_def inv_thd_waitq_def)
   apply (metis (no_types, lifting) list.set_sel(2))
  apply(subgoal_tac "let Vx = V
          \<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
             get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
             OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
             need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
             thd_state := (thd_state V)
               (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
                SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
             ret := (ret V)(t := OK)\<rparr>
    in inv_thd_waitq_midx Vx (hd (wait_q (OSMailbox_info V pevent)))")
  prefer 2
   apply(simp add:inv_waitq_to_inv_waitqx)apply auto
  apply(rule  waitq_midx_and_Ready_eq_waitq5)
  apply blast            (*just need to prove that:thd_state hd(wait_q) V' = READY  *)
  apply auto
  subgoal 1
proof -
  assume a1: "t = hd (wait_q (OSMailbox_info V pevent))"
  assume a2: "wait_q (OSMailbox_info V pevent) \<noteq> []"
  assume a3: "pevent \<in> OSMailBoxs V"
assume a4: "inv_thd_waitq V"
  assume a5: "cur V = Some (hd (wait_q (OSMailbox_info V pevent)))"
assume a6: "inv_cur V"
have "thd_state V t = BLOCKED"
using a4 a3 a2 a1 by (simp add: inv_thd_waitq_def)
then show False
  using a6 a5 a1 by (metis (no_types) Thread_State_Type.distinct(5) inv_cur_def)
qed

  subgoal 1
    apply(simp add:inv_thd_waitq_def)
    by (metis Thread_State_Type.distinct(5) hd_in_set inv_cur_def)
    

done

text \<open>this lemma is to show that: inv V \<Longrightarrow> inv V'\<close>
lemma V'_sat_INV:"msg = Some y \<Longrightarrow>
    pevent \<in> OSMailBoxs V \<Longrightarrow>
    V \<in> OSMboxPost_pre t \<Longrightarrow>
    cur V = Some t \<Longrightarrow>
    wait_q (OSMailbox_info V pevent) \<noteq> [] \<Longrightarrow>
    V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
        get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
        OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
        need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
        thd_state := (thd_state V)
          (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
           SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
        ret := (ret V)(t := OK)\<rparr>
    \<in> OSMboxPost_post t "
  apply(simp add:OSMboxPost_post_def)
  apply(case_tac"V = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
          get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
          OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
          need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
          thd_state := (thd_state V)
            (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
             SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
          ret := (ret V)(t := OK)\<rparr> ")
   apply(simp add:OSMboxPost_pre_def)
  apply(simp add:OSMboxPost_pre_def)

  apply(simp add:inv_def)
  apply(rule conjI)
apply(simp add:inv_cur_def)
   apply auto[1]
  apply(subgoal_tac "let Vx =  V
       \<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
       get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
       OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
       need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
       thd_state := (thd_state V)
         (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
          SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
       ret := (ret V)(t := OK)\<rparr> in
                     inv_thd_waitq_mid5 Vx (hd(wait_q (OSMailbox_info V pevent)))")

  apply(simp add:inv_thd_waitq_mid5_def inv_thd_waitq_def)
   apply (metis (no_types, lifting) list.set_sel(2))
  apply(subgoal_tac "let Vx = V
          \<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
             get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y), statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
             OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
             need_resched := (need_resched V)(t := True), cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
             thd_state := (thd_state V)
               (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
                SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
             ret := (ret V)(t := OK)\<rparr>
    in inv_thd_waitq_midx Vx (hd (wait_q (OSMailbox_info V pevent)))")
  prefer 2
   apply(simp add:inv_waitq_to_inv_waitqx)apply auto
  apply(rule  waitq_midx_and_Ready_eq_waitq5)
  apply blast            (*just need to prove that:thd_state hd(wait_q) V' = READY  *)
  apply auto
  subgoal 1
proof -
  assume a1: "t = hd (wait_q (OSMailbox_info V pevent))"
  assume a2: "wait_q (OSMailbox_info V pevent) \<noteq> []"
  assume a3: "pevent \<in> OSMailBoxs V"
assume a4: "inv_thd_waitq V"
  assume a5: "cur V = Some (hd (wait_q (OSMailbox_info V pevent)))"
assume a6: "inv_cur V"
have "thd_state V t = BLOCKED"
using a4 a3 a2 a1 by (simp add: inv_thd_waitq_def)
then show False
  using a6 a5 a1 by (metis (no_types) Thread_State_Type.distinct(5) inv_cur_def)
qed

  subgoal 1
    apply(simp add:inv_thd_waitq_def)
    by (metis Thread_State_Type.distinct(5) hd_in_set inv_cur_def)
  
done

text \<open>
the key steps to prove this lemma:
\<bullet> Get the state V' when the event code ends
\<bullet> prove that (V,V')\<in>OSMboxPost_guar t
\<bullet> prove that inv V'
\<bullet> prove that  stable (\<lbrace>\<acute>(Pair V) \<in> OSMboxPost_guar t\<rbrace> \<inter> OSMboxPost_post t) {(x, y). x = y}

!! trick:
   to use the type V\<lparr>...\<rparr>, we should eliminate the quantifier  ‘\<And>’
\<close>
lemma OSMboxPost_satRG_h1_1:" msg = Some y \<Longrightarrow>
           pevent \<in> OSMailBoxs V \<Longrightarrow>
           V \<in> OSMboxPost_pre t \<Longrightarrow>
           cur V = Some t \<Longrightarrow>
           \<turnstile>\<^sub>I (W\<acute>th := \<acute>th(t := hd (wait_q (\<acute>OSMailbox_info pevent)));; \<acute>tmout := \<acute>tmout(\<acute>th t := OK);; \<acute>get_msg := \<acute>get_msg(\<acute>th t \<mapsto> y);;
                  \<acute>statPend := \<acute>statPend(\<acute>th t := OS_STAT_PEND_OK);;
                  \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>wait_q := tl (wait_q (\<acute>OSMailbox_info pevent))\<rparr>);;
                  \<acute>thd_state := \<acute>thd_state(\<acute>th t := READY);;
                  \<acute>need_resched := \<acute>need_resched(t := True);;
                  IF \<acute>need_resched t THEN reschedule FI;;
                  \<acute>ret := \<acute>ret
                  (t := OK)) sat\<^sub>p [{V} \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>, {(x, y). x = y}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMboxPost_guar t\<rbrace> \<inter> OSMboxPost_post t]"

  apply(case_tac "wait_q (OSMailbox_info V pevent) = []")
   apply auto
   apply(simp add:Emptyprecond)   
  apply(simp add:reschedule_def)    \<comment> \<open>use this method to extract the assumption "wait_q (\<acute>OSMailbox_info pevent) \<noteq> []" \<close>


    apply(rule Seq[where mid = "let V9 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                    get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                    statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
                                    OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                    need_resched := (need_resched V)(t := True),
                                    thd_state := (thd_state V)(hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY),
                                    cur :=
                                      Some
                                       (SOME ta.
                                           ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow>
                                           ta \<noteq> t \<longrightarrow>
                                           thd_state V ta =
                                           READY)\<rparr>  in
                                {V9\<lparr>thd_state := (thd_state V9)(the (cur V9) := RUNNING)\<rparr>}"]) 
 apply(rule Seq[where mid = "let V6 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                    get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                    statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
                                    OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                    thd_state := (thd_state V)
                                      (hd (wait_q (OSMailbox_info V pevent)) :=
                                         READY)\<rparr>  in
                                    {V6\<lparr>need_resched := (need_resched V6)( t := True)\<rparr>}"]) 
   apply(rule Seq[where mid = "let V5 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                  get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                  statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
                                  OSMailbox_info := (OSMailbox_info V)
                                    (pevent := OSMailbox_info V pevent
                                       \<lparr>wait_q :=
                                          tl (wait_q
                                               (OSMailbox_info V
                                                 pevent))\<rparr>)\<rparr>  in
                               {V5\<lparr>thd_state := (thd_state V5)((th V5) t := READY)\<rparr>}"]) 
     apply(rule Seq[where mid = "let V4 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))),
                                                tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                                get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                                statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK)\<rparr> in
                                      {V4\<lparr>OSMailbox_info := (OSMailbox_info V4)(pevent := OSMailbox_info V4 pevent
                                         \<lparr>wait_q := tl (wait_q (OSMailbox_info V4 pevent))\<rparr>)\<rparr>} (* \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>*)"])  
  apply(rule Seq[where mid = "let V3 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                         get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y)\<rparr> in
                                      {V3\<lparr>statPend := (statPend V3)((th V3) t := OS_STAT_PEND_OK)\<rparr>} \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
    apply(rule Seq[where mid = "let V2 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK)\<rparr> in
                                      {V2\<lparr>get_msg := (get_msg V2)((th V2) t := msg)\<rparr>} \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
        apply(rule Seq[where mid = "let V1 = V\<lparr>th := (th V)(t :=  hd (wait_q((OSMailbox_info V) pevent)))\<rparr> in
                                      {V1\<lparr>tmout := (tmout V1)((th V1) t := OK)\<rparr>} \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
         apply(rule Seq[where mid = "{V\<lparr>th := (th V)(t :=  hd (wait_q((OSMailbox_info V) pevent)))\<rparr>} \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
          
          apply(rule Basic) apply auto 
           apply(simp add:stable_id2)  apply(simp add:stable_id2)
         apply(rule Basic)apply auto
          apply(simp add:stable_id2) apply(simp add:stable_id2)
        apply(rule Basic)apply auto
         apply(simp add:stable_id2) apply(simp add:stable_id2)
       apply(rule Basic)apply auto
        apply(simp add:stable_id2) apply(simp add:stable_id2)
      apply(rule Basic)apply auto
       apply(simp add:stable_id2) apply(simp add:stable_id2)
     apply(rule Basic)apply auto
      apply(simp add:stable_id2) apply(simp add:stable_id2)
    apply(rule Basic)apply auto
     apply(simp add:stable_id2) apply(simp add:stable_id2)

   apply(rule Cond)  apply(simp add:stable_id2)
 apply(rule Seq[where mid = "let V8 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                    get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                    statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
                                    OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                    need_resched := (need_resched V)(t := True),
                                    thd_state := (thd_state V)
                                    (hd (wait_q (OSMailbox_info V pevent)) := READY,
                                       t := READY)\<rparr>  in
                                 {V8 \<lparr>cur :=  Some (SOME t. (thd_state V8) t = READY)\<rparr>}"]) 
 apply(rule Seq[where mid = "let V7 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OK),
                                  get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                  statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
                                  OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                  thd_state := (thd_state V)(hd (wait_q (OSMailbox_info V pevent)) := READY), need_resched := (need_resched V)(t := True)\<rparr>  in
                                  {V7  \<lparr>thd_state := (thd_state V7)((the (cur V7)) := READY)\<rparr>}"]) 
       apply(rule Basic) apply auto
       apply(simp add:stable_id2) apply(simp add:stable_id2)
     apply(rule Basic) apply auto
      apply(simp add:stable_id2) apply(simp add:stable_id2)
 apply(rule Basic) apply auto
     apply(simp add:stable_id2) apply(simp add:stable_id2)
   apply(simp add:Emptyprecond)
  apply(rule Basic) apply auto
     apply(simp add:OSMboxPost_pre_def OSMboxPost_post_def) 


    (*1. use lemma VV'_in_OSMboxPost_guar *)
  apply(simp add:VV'_in_OSMboxPost_guar)
    (*2. use lemma V'_sat_INV : prove that V' satifies: inv V' *)
  apply(simp add:V'_sat_INV)
   apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  done

lemma  OSMboxPost_satRG_h1_2:"
    msg = Some y \<Longrightarrow>
    pevent \<in> OSMailBoxs V \<Longrightarrow>
    V \<in> OSMboxPost_pre t \<Longrightarrow>
    cur V = Some t \<Longrightarrow>
    \<turnstile>\<^sub>I (W IF \<exists>y. msgPtr (\<acute>OSMailbox_info pevent) = Some y THEN \<acute>ret := \<acute>ret(t := OS_ERR_MBOX_FULL)
           ELSE \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>msgPtr := Some y\<rparr>);; \<acute>ret := \<acute>ret(t := OK)
           FI) sat\<^sub>p [{V} \<inter> -\<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>, {(x, y). x = y}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMboxPost_guar t\<rbrace> \<inter> OSMboxPost_post t]"

   apply(case_tac "wait_q (OSMailbox_info V pevent) \<noteq> []")
   apply auto
   apply(simp add:Emptyprecond)  

  apply(case_tac "\<exists>y. msgPtr (OSMailbox_info V pevent) = Some y")
  subgoal 1
    apply(rule Cond)
       apply(simp add:stable_def)
      apply(rule Basic)apply auto
        apply(simp add:OSMboxPost_pre_def OSMboxPost_guar_def inv_def inv_cur_def inv_thd_waitq_def)
        apply(simp add:gvars_conf_def gvars_conf_stable_def lvars_nochange_lemma_def)
       apply(simp add:OSMboxPost_pre_def OSMboxPost_guar_def OSMboxPost_post_def inv_def inv_cur_def inv_thd_waitq_def)
       apply auto
      apply(simp add:stable_id2)
    apply(simp add:stable_id2)
    apply(simp add:Emptyprecond)
    done

  subgoal 1
    apply(rule Cond)
    apply(simp add:stable_id2)
    apply(rule Basic)apply auto
    apply(simp add:stable_id2)
    apply(simp add:stable_id2)
     apply(rule Seq[where mid = "{V\<lparr>  OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>msgPtr := Some y\<rparr>) \<rparr>}"]) 
     apply(rule Basic)apply auto
apply(simp add:stable_id2)
     apply(simp add:stable_id2)
    apply(rule Basic)apply auto
       apply(simp add:OSMboxPost_pre_def OSMboxPost_guar_def OSMboxPost_post_def inv_def inv_cur_def inv_thd_waitq_def)
       apply(simp add:gvars_conf_def gvars_conf_stable_def lvars_nochange_lemma_def)
       apply (metis length_pos_if_in_set less_numeral_extra(3) list.size(3))
    apply(simp add:OSMboxPost_pre_def OSMboxPost_guar_def OSMboxPost_post_def inv_def inv_cur_def inv_thd_waitq_def)
      apply fastforce
     apply(simp add:stable_id2)
    apply(simp add:stable_id2)
    done
  done


lemma OSMboxPost_satRG_h1:" \<And>y V.  msg = Some y \<Longrightarrow>
           OSMboxPost_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {V} \<noteq> {} \<Longrightarrow>
           \<turnstile>\<^sub>I (W Await UNIV
                   (IF wait_q (\<acute>OSMailbox_info pevent) \<noteq> []
                    THEN \<acute>th := \<acute>th(t := hd (wait_q (\<acute>OSMailbox_info pevent)));; \<acute>tmout := \<acute>tmout(\<acute>th t := OK);; \<acute>get_msg := \<acute>get_msg(\<acute>th t \<mapsto> y);;
                         \<acute>statPend := \<acute>statPend(\<acute>th t := OS_STAT_PEND_OK);;
                         \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>wait_q := tl (wait_q (\<acute>OSMailbox_info pevent))\<rparr>);;
                         \<acute>thd_state := \<acute>thd_state(\<acute>th t := READY);;
                         \<acute>need_resched := \<acute>need_resched(t := True);;
                         IF \<acute>need_resched t THEN reschedule FI;;
                         \<acute>ret := \<acute>ret(t := OK)
                    ELSE IF \<exists>y. msgPtr (\<acute>OSMailbox_info pevent) = Some y THEN \<acute>ret := \<acute>ret(t := OS_ERR_MBOX_FULL)
                         ELSE \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>msgPtr := Some y\<rparr>);; \<acute>ret := \<acute>ret(t := OK)FI
                    FI)) sat\<^sub>p [OSMboxPost_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter>
                                {V}, {(s, t). s = t}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMboxPost_guar t\<rbrace> \<inter> OSMboxPost_post t] "
  apply auto 
  apply(rule Await) 
    apply(simp add: stable_id2)
  apply(simp add: stable_id2)
  apply auto
  apply(case_tac "{V} \<inter> {Va}={}")
   apply auto
   apply(simp add:Emptyprecond)
  apply(rule Cond)
     apply(simp add:stable_id2)
    apply(simp add:OSMboxPost_satRG_h1_1)
 apply(simp add:OSMboxPost_satRG_h1_2)
  apply auto
  done


lemma OSMboxPost_satRG_lemma: "\<Gamma> (OSMboxPost t pevent msg) \<turnstile> OSMboxPost_RGCond_lemma t"
  apply (simp add:Evt_sat_RG_def)
  apply (simp add:OSMboxPost_def OSMboxPost_RGCond_lemma_def)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  apply(unfold stm_def)
  apply auto  apply (rule BasicEvt)
     apply(simp add:body_def)
     apply(rule Cond)
        apply(simp add:guard_def stable_def) apply auto
    apply(simp add:OSMboxPost_pre_def OSMboxPost_rely_lemma_def
              OSMboxPost_guar_def OSMboxPost_post_def)apply auto
    apply(simp add:OSMboxPost_pre_def OSMboxPost_rely_lemma_def
              OSMboxPost_guar_def OSMboxPost_post_def)
        apply (simp add:gvars_conf_stable_def gvars_conf_def)apply auto
  apply(rule Await)
         apply(simp add:guard_def)
         apply(simp add: OSMboxPost_pre_stable)
        apply(simp add: OSMboxPost_post_stable)
  using Emptyprecond apply auto[1]
       apply (simp add: Emptyprecond)

  apply (rule Basic)                                                                       \<comment> \<open>msg = None,return OS_ERR_POST_NULL directly.(Basic) \<close>
     apply (simp add:guard_def OSMboxPost_guar_def gvars_conf_stable_def inv_def
           OSMboxPost_post_def gvars_conf_def  OSMboxPost_pre_def)
     apply auto
  apply (simp add:inv_cur_def)
       apply (simp add:inv_thd_waitq_def)apply auto
      apply(simp add:lvars_nochange_lemma_def)
     apply(simp add:inv_cur_def)
    apply(simp add:inv_thd_waitq_def)apply auto
   apply(simp add:stable_def)
       apply (rule stable_id2)                                                          \<comment> \<open>end \<close>   


      apply(rule Await)
        apply(simp add:stable_def)
       apply(simp add: OSMboxPost_post_stable)
      apply auto apply(rule Await)
        apply(simp add:stable_def)apply(rule stable_id2)
  using Emptyprecond apply auto[1]         \<comment> \<open> OSMboxPost_satRG_h2 \<close>

    
     apply(simp add: OSMboxPost_guar_def)
  using OSMboxPost_post_def OSMboxPost_post_stable OSMboxPost_pre_def apply auto[1]
  apply(simp add:OSMboxPost_guar_def)             \<comment> \<open> situation 1: msg = None -------   prove end \<close>


 apply(rule BasicEvt)                            \<comment> \<open> situation 2: msg \<noteq> None \<close>
  apply(simp add:body_def) 
    apply (rule Cond)
       apply(simp add:stable_def guard_def)apply auto

 apply(simp add:OSMboxPost_pre_def OSMboxPost_rely_lemma_def
              OSMboxPost_guar_def OSMboxPost_post_def)apply auto
    apply(simp add:OSMboxPost_pre_def OSMboxPost_rely_lemma_def
              OSMboxPost_guar_def OSMboxPost_post_def)
        apply (simp add:gvars_conf_stable_def gvars_conf_def)apply auto
  apply(rule Await)
         apply(simp add:stable_def)+
  apply (meson OSMboxPost_post_stable stable_def)
  using Emptyprecond apply auto[1]   
     prefer 2 apply (simp add:OSMboxPost_guar_def)
    prefer 2   apply(simp add:OSMboxPost_pre_def OSMboxPost_rely_lemma_def stable_def gvars_conf_stable_def gvars_conf_def)
   prefer 2 apply(simp add:OSMboxPost_guar_def)
  apply(simp add:guard_def)
     apply (rule Await)                           \<comment> \<open> situation 2: msg \<noteq> None \<close>
  apply (simp add: OSMboxPost_pre_stable)
   apply(simp add: OSMboxPost_post_stable) apply auto
  apply(case_tac "OSMboxPost_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter>
                                {V} = {}")
   apply(simp add:OSMboxPost_pre_def) 
   apply(rule Await) 
     apply(simp add:stable_id2)  apply(simp add:stable_id2)

   apply(simp add:Emptyprecond)                \<comment> \<open> situation 1: pevent \<notin> OSmailboxs \<close> 



 apply auto                   \<comment> \<open>apply simp add:OSMboxPost_satRG_h1.  It's not able to apply OSMboxPost_satRG1 directly \<close> 
  apply(rule Await) 
    apply(simp add: stable_id2)
  apply(simp add: stable_id2)
  apply auto
  apply(case_tac "{V} \<inter> {Va}={}")
   apply auto
   apply(simp add:Emptyprecond)
  apply(rule Cond)
     apply(simp add:stable_id2)
    apply(simp add:OSMboxPost_satRG_h1_1)
 apply(simp add:OSMboxPost_satRG_h1_2)
  apply auto
  done

lemma lemma_trans:"rghoare_e \<Gamma> (OSMboxPost t pevent msg) (Pre\<^sub>f (OSMboxPost_RGCond_lemma t)) (Rely\<^sub>f (OSMboxPost_RGCond_lemma t)) (Guar\<^sub>f (OSMboxPost_RGCond_lemma t))
     (Post\<^sub>f (OSMboxPost_RGCond_lemma t)) =  \<Gamma> (OSMboxPost t pevent msg) \<turnstile> OSMboxPost_RGCond_lemma t"
  apply(simp add:Evt_sat_RG_def)
  done

lemma OSMboxPost_satRG: "\<Gamma> (OSMboxPost t pevent msg) \<turnstile> OSMboxPost_RGCond t"
  apply (simp add:Evt_sat_RG_def)
  apply(rule Evt_conseq[where  pre' = "Pre\<^sub>f (OSMboxPost_RGCond_lemma t)" and
                              rely' = "Rely\<^sub>f (OSMboxPost_RGCond_lemma t)" and
                              guar' = "Guar\<^sub>f (OSMboxPost_RGCond_lemma t)" and 
                              post' = "Post\<^sub>f (OSMboxPost_RGCond_lemma t)" ])
      apply(simp add:Pre\<^sub>f_def OSMboxPost_RGCond_def OSMboxPost_RGCond_lemma_def getrgformula_def)
     apply(simp add:Rely\<^sub>f_def OSMboxPost_RGCond_def OSMboxPost_RGCond_lemma_def getrgformula_def)
     apply(simp add:OSMboxPost_rely_def OSMboxPost_rely_lemma_def)
     apply(simp add:lvars_nochange_lemma_rel_def lvars_nochange_rel_def) apply auto
          apply(simp add:lvars_nochange_lemma_def lvars_nochange_def) 
  apply(simp add:lvars_nochange_lemma_def lvars_nochange_def) 
  apply(simp add:lvars_nochange_lemma_def lvars_nochange_def) 
  apply(simp add:lvars_nochange_lemma_def lvars_nochange_def) 
  apply(simp add:lvars_nochange_lemma_def lvars_nochange_def) 
  apply(simp add:lvars_nochange_lemma_def lvars_nochange_def) 
   apply(simp add:Guar\<^sub>f_def OSMboxPost_RGCond_def OSMboxPost_RGCond_lemma_def getrgformula_def)
   apply(simp add:Post\<^sub>f_def OSMboxPost_RGCond_def OSMboxPost_RGCond_lemma_def getrgformula_def)
  apply(subst lemma_trans) 

  apply(simp add: OSMboxPost_satRG_lemma)
  done




end