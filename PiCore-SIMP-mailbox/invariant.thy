theory invariant
imports mem_spec "HOL-Eisbach.Eisbach_Tools" (*"~~/src/HOL/Word/Word"*)
begin

text\<open>
this theory defines the invariant and its lemmas.
\<close>

section \<open>invariants\<close>

subsection \<open>defs of invariants\<close>
text\<open>
we consider multi-threaded execution on mono-core.
A thread is the currently executing thread iff it is in RUNNING state.
\<close>
definition inv_cur :: "State \<Rightarrow> bool"
where "inv_cur s \<equiv> \<forall>t. cur s = Some t \<longleftrightarrow> thd_state s t = RUNNING"


abbreviation dist_list :: "'a list \<Rightarrow> bool"
where "dist_list l \<equiv> \<forall>i j. i < length l \<and> j < length l \<and> i \<noteq> j \<longrightarrow> l!i \<noteq> l!j"                      \<comment> \<open> elements in a list are different with each other    \<close>



text\<open>
the relation of thread state and wait queue.
here we dont consider other modules of zephyr, so blocked thread is in wait que of mailboxs. 
\<close>
definition inv_thd_waitq :: "State \<Rightarrow> bool"
where "inv_thd_waitq s \<equiv> 
  (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                 \<comment> \<open> thread in waitq is BLOCKED    \<close>
 \<and> (\<forall>t. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))       \<comment> \<open> BLOCKED thread is in a waitq    \<close>
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  \<comment> \<open>  threads in a waitq are different with each other, which means
                                                                                                    a thread could not waiting for the same pool two times    \<close>
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q))))"       \<comment> \<open>threads of two waitqs are different, which means 
                                                                                                     a thread could not waiting for two pools    \<close>


definition inv_thd_waitq_mid :: "State \<Rightarrow>Thread \<Rightarrow> bool"
where "inv_thd_waitq_mid s tx \<equiv> 
  (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                 \<comment> \<open> thread in waitq is BLOCKED    \<close>
 \<and>(\<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))       \<comment> \<open> BLOCKED thread is in a waitq    \<close>
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  \<comment> \<open>  threads in a waitq are different with each other, which means
                                                                                                    a thread could not waiting for the same pool two times    \<close>
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q))))"       \<comment> \<open>threads of two waitqs are different, which means 
                                                                                                     a thread could not waiting for two pools    \<close>

definition inv_thd_waitq_mid0 :: "State  \<Rightarrow> bool"
where "inv_thd_waitq_mid0 s  \<equiv> 
  (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                  
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q)))) "  

definition inv_thd_waitq_mid1 :: "State \<Rightarrow>Thread  \<Rightarrow> bool"
where "inv_thd_waitq_mid1 s tx \<equiv>
  \<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p)))
 \<and> thd_state s tx = BLOCKED "

definition inv_thd_waitq_mid2 :: "State \<Rightarrow>Thread  \<Rightarrow> bool"
where "inv_thd_waitq_mid2 s tx \<equiv>
 ( \<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))
 \<and> thd_state s tx = READY "

definition inv_thd_waitq_mid3 :: "State \<Rightarrow> bool"                   (* inv_thd_waiq = inv_thd_waitq_mid0 + inv_thd_waitq_mid3 *)
where "inv_thd_waitq_mid3 s  \<equiv>
  (\<forall>t . thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))"



definition inv_thd_waitq_mid4 :: "State \<Rightarrow>Thread  \<Rightarrow> bool"         (* inv_thd_waiq_mid4 = inv_thd_waitq_mid0 + inv_thd_waitq_mid1 *)
where "inv_thd_waitq_mid4 s tx \<equiv>
 ( \<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))
 \<and> thd_state s tx = BLOCKED \<and> (\<forall>p\<in>OSMailBoxs s. tx \<notin>  set (wait_q (OSMailbox_info s p)))
 \<and> (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                  
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q)))) "

definition inv_thd_waitq_midx :: "State \<Rightarrow>Thread  \<Rightarrow> bool"         (* inv_thd_waiq_mid4 = inv_thd_waitq_mid0 + inv_thd_waitq_mid1 *)
where "inv_thd_waitq_midx s tx \<equiv>
 ( \<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))
 \<and> (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                  
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q)))) "


lemma waitq_to_waitq_midx:"pevent \<in> OSMailBoxs V \<Longrightarrow> inv_thd_waitq V \<Longrightarrow> inv_thd_waitq_midx V (hd(wait_q (OSMailbox_info V pevent)))"
  apply(simp add:inv_thd_waitq_def inv_thd_waitq_midx_def)
  apply auto
  done




definition inv_thd_waitq_mid5 :: "State \<Rightarrow>Thread  \<Rightarrow> bool"                 (* inv_thd_waiq_mid5 = inv_thd_waitq_mid0 + inv_thd_waitq_mid2 *)
where "inv_thd_waitq_mid5 s tx \<equiv>
 ( \<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))
 \<and> thd_state s tx = READY 
 \<and> (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                  
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q)))) "


definition inv_thd_waitq_mid6 :: "State \<Rightarrow>Thread  \<Rightarrow> bool"                 (* inv_thd_waiq_mid5 = inv_thd_waitq_mid0 + inv_thd_waitq_mid2 *)
where "inv_thd_waitq_mid6 s tx \<equiv>
 ( \<forall>t \<noteq> tx. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))
 \<and> thd_state s tx = READY 
 \<and> (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). t\<noteq>tx \<longrightarrow> thd_state s t = BLOCKED)                  
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                  
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q)))) "

lemma sad:"\<forall>t tx s. inv_thd_waitq_mid5 s tx \<Longrightarrow> \<forall>s. inv_thd_waitq s"
  apply(simp add:inv_thd_waitq_mid6_def inv_thd_waitq_def)apply auto




lemma mid2_to_mid3:"\<forall>t tx s. inv_thd_waitq_mid2 s tx \<and> inv_thd_waitq_mid0 s  \<Longrightarrow> \<forall>s . inv_thd_waitq_mid3 s \<and> inv_thd_waitq_mid0 s \<Longrightarrow>  \<forall>s. inv_thd_waitq s"
  apply(simp add:inv_thd_waitq_def inv_thd_waitq_mid_def inv_thd_waitq_mid2_def inv_thd_waitq_mid3_def inv_thd_waitq_mid0_def)
  done

lemma mid:"\<forall>t tx s. inv_thd_waitq_mid5 s tx \<Longrightarrow> \<forall>t s. inv_thd_waitq s"
  apply(simp add:inv_thd_waitq_mid5_def inv_thd_waitq_def mid2_to_mid3)
  apply(metis (full_types) Thread_State_Type.distinct(3) length_greater_0_conv nth_mem)
  done


lemma mid2:"\<forall>t x. inv_thd_waitq x \<Longrightarrow> \<forall>t x pevent. pevent \<in> OSMailBoxs x\<longrightarrow> inv_thd_waitq x\<lparr>OSMailbox_info := (OSMailbox_info x)(pevent := OSMailbox_info x pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info x pevent))\<rparr>)\<rparr>"    



definition inv :: "State \<Rightarrow> bool"
where "inv s \<equiv> inv_cur s \<and> inv_thd_waitq s"



method simp_inv = (simp add:inv_def  inv_thd_waitq_def)

method unfold_inv = (unfold inv_def inv_thd_waitq_def inv_cur_def)[1]


subsection \<open>initial state $s_0$\<close>

text\<open>
we dont consider mailbox_init, only define s0 to show the state after memory pool initialization.
\<close>
axiomatization s0::State where
  s0a1: "cur s0 = None" and
  s0a2: "tick s0 = 0" and
  s0a3: "thd_state s0 = (\<lambda>t. READY)" and
  s0a4: "OSMailBoxs s0 \<noteq> {}" and
  s0a5: "\<forall>p\<in>OSMailBoxs s0. wait_q (OSMailbox_info s0 p) = []" and
  s0a6: "\<forall>p\<in>OSMailBoxs s0. let mp = OSMailbox_info s0 p in  msgPtr mp = None" 



lemma s0_inv_cur: "inv_cur s0"
  apply (simp add: inv_cur_def)
  apply (simp add: s0a1 s0a3)
  done


lemma s0_inv_thd_waitq: "inv_thd_waitq s0"
  apply(simp add: inv_thd_waitq_def)
  apply(simp add: s0a1 s0a2 s0a3 s0a4 s0a5)
  done

lemma s0_inv: "inv s0"
  apply(unfold inv_def)
  using s0_inv_cur apply simp
  using s0_inv_thd_waitq apply simp
  done

(*====================================================================*)
lemma sat:"stable {s. inv s} {(s,t). inv s \<longrightarrow> inv t} "
  apply(simp add:stable_def)
  done

lemma asdtt:"stable A C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> stable A B"
  apply(simp add:stable_def)
  apply auto
  done

lemma tt:"\<Gamma> (Event) \<turnstile> RG[A,B,C,D] \<Longrightarrow> R\<subseteq>B \<Longrightarrow> \<Gamma> (Event) \<turnstile> RG[A,R,C,D]"
  apply (simp add:Evt_sat_RG_def)
  apply(simp add:Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  by (metis Evt_conseq order_refl)
(*\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>\<comment>*)
term "UNIV"   
lemma testq:"\<lbrace>True\<rbrace> = UNIV"
  apply auto
  done
lemma tst:"stable \<lbrace>True\<rbrace> \<lbrace>True\<rbrace>"
  apply auto
  apply(simp add:stable_def)
  done
(*{(s,t). s = t} \<equiv> Id"*)
lemma tst2:"{(s,t). s = t} = Id"
  apply auto
  done
(*=====================================================================*)



end
