theory mailbox_management_inv
  imports mailbox_manage_sys 
begin

lemma tick_guar_stb_inv:" stable (Collect invariant.inv) Tick_guar"
  apply(simp add:inv_def Tick_guar_def stable_def inv_cur_def inv_thd_waitq_def)
  apply auto
  done

section \<open> invariant verification \<close>
theorem "invariant_presv_pares \<Gamma> inv (paresys_spec Mailbox_manage_system_Spec) {s0} sys_rely"
  apply(rule invariant_theorem[where G="sys_guar" and pst = UNIV])
    using mailbox_sys_sat apply fast
    apply(simp add:sys_rely_def stable_def)
    apply(simp add:sys_guar_def)
    apply(rule stable_un_R) apply(rule stable_un_R) 
      using tick_guar_stb_inv apply(simp add:stable_def)
      using sched_guar_stb_inv apply(simp add:stable_def)
       apply(rule stable_un_S) apply clarify      
       apply(rule stable_un_R) 
        apply(rule stable_un_R)
      using OSMboxPost_guar_stb_inv  apply(simp add:stable_def) 
      using OSMboxAccept_guar_stb_inv apply(simp add:stable_def)
      using OSMboxPend_guar_stb_inv apply(simp add:stable_def)
        using OSMboxAccept_guar_stb_inv OSMboxPend_guar_stb_inv (* apply(simp add:stable_def) *)
        apply(simp add:s0_inv)
        done
end