theory List_aux
imports aux_lemma
begin

primrec list_updates :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_updates [] i1 i2 v = []" |
  "list_updates (x#xs) i1 i2 v = 
    (case i1 of 0 \<Rightarrow> (if i2 > 0 then v # list_updates xs 0 (i2 - 1) v else (v#xs) ) | 
                Suc j \<Rightarrow> (if i2 > j then x # list_updates xs j (i2 - 1) v else (x#xs) ))"

value "list_updates [1::nat,2,3,4,5] 9 0 6"

lemma length_list_update2 [simp]: "length (list_updates l i1 i2 v) = length l"
  apply(induct l arbitrary: i1 i2 v)
    apply simp
    apply(case_tac "i1") 
      apply(case_tac "i2") apply simp+
  done

lemma list_updates_eq [simp]: "\<lbrakk>i1 \<le> i; i \<le> i2; i2 < length l\<rbrakk> \<Longrightarrow> (list_updates l i1 i2 v)!i = v"
  apply(induct l arbitrary: i i1 i2 v)
    apply simp
    apply(case_tac "i1") apply auto
      apply(case_tac "i2") apply simp 
    by (metis (no_types, lifting) One_nat_def Suc_less_SucD diff_Suc_1 
          le_SucE le_zero_eq not_less_eq_eq nth_Cons' zero_induct) 

lemma list_updates_neq [simp]: "i < i1 \<or> i > i2 \<Longrightarrow> (list_updates l i1 i2 v)!i = l!i"
  apply(induct l arbitrary: i i1 i2 v)
    apply simp 
    apply(case_tac "i1") apply simp
    apply(case_tac "i2") apply simp apply(case_tac "i") apply simp+
  done

lemma list_updates_beyond[simp]: "i1 \<ge> length l \<Longrightarrow> (list_updates l i1 i2 v) = l"
  apply(induct l arbitrary: i1 i2 v)
    apply simp apply(case_tac "i1") by auto

lemma list_updates_beyond2[simp]: "i2 < i1 \<Longrightarrow> (list_updates l i1 i2 v) = l"
  apply(induct l arbitrary: i1 i2 v)
    apply simp apply(case_tac "i1") by auto

lemma list_updates_nonempty[simp]: "(list_updates l i1 i2 v) = [] \<longleftrightarrow> l = []"
  by (metis length_greater_0_conv length_list_update2)
  
lemma list_updates_same_conv: 
  "i1 < length l \<and> i2 < length l \<Longrightarrow> ((list_updates l i1 i2 v) = l) = (\<forall>i. i \<ge> i1 \<and> i \<le> i2 \<longrightarrow> l ! i = v)"
  apply(induct l arbitrary: i1 i2 v) 
    apply simp
    apply(case_tac "i1 \<le> i2") apply(rule iffI)
      apply (metis list_updates_eq) 
      apply (smt length_list_update2 list_updates_eq list_updates_neq not_le_imp_less nth_equalityI)
  by (metis (mono_tags, lifting) list_updates_beyond2 list_updates_eq not_le_imp_less) 
    
lemma list_updates_append1:
  "i2 < length l \<Longrightarrow> list_updates (l @ t) i1 i2 v = list_updates l i1 i2 v @ t"
  apply(induct l arbitrary: i1 i2 v) 
    apply simp
    apply(case_tac "i1 \<le> i2")
      apply(case_tac "i1") apply simp 
      apply(case_tac "i2") apply simp apply auto[1]
  by (metis list_updates_beyond2 not_less)
    

primrec list_updates_fstn :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_updates_fstn [] n v = []" |
  "list_updates_fstn (x#xs) n v = 
    (case n of 0 \<Rightarrow> x#xs | Suc m \<Rightarrow> v#list_updates_fstn xs m v)"

primrec list_updates_n :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_updates_n [] i n v = []" |
  "list_updates_n (x#xs) i n v = 
    (case i of 0 \<Rightarrow> list_updates_fstn (x#xs) n v | Suc j \<Rightarrow> x#list_updates_n xs j n v)"

value "list_updates_n [1::nat,2,3,4,5] 0 9 6"

lemma length_list_update_fstn [simp]: "length (list_updates_fstn l n v) = length l"
  apply(induct l arbitrary: n v)
    apply simp apply(case_tac "n") apply simp+
done

lemma length_list_update_n [simp]: "length (list_updates_n l i n v) = length l"
  apply(induct l arbitrary: i n v)
    apply simp
    apply(case_tac "i") 
      apply(case_tac "n") apply simp+
  done

lemma list_updates_fstn_eq [simp]: "\<lbrakk>i < length l; i < n\<rbrakk> \<Longrightarrow> (list_updates_fstn l n v)!i = v"
  apply(induct l arbitrary: i n v) apply simp
    apply(case_tac "i") 
    apply(case_tac "n") apply simp+  
    apply(case_tac "n") apply simp+
done

lemma list_updates_n_eq [simp]: "\<lbrakk>i \<le> j; j < length l; j < i + n\<rbrakk> \<Longrightarrow> (list_updates_n l i n v)!j = v"
  apply(induct l arbitrary: i j n v) apply simp
    apply(case_tac "i") apply auto
    apply(case_tac "n") apply auto
  using less_Suc_eq_0_disj by auto

lemma list_updates_fst0 [simp]: "list_updates_fstn l 0 v = l"
  apply(induct l arbitrary: v) by simp+

lemma list_updates_0 [simp]: "list_updates_n l i 0 v = l"
  apply(induct l arbitrary: i v) apply simp apply(case_tac "i") apply simp+
done

lemma list_updates_fstn_neq [simp]: "j \<ge>  n \<Longrightarrow> (list_updates_fstn l n v)!j = l!j"
  apply(induct l arbitrary: j n v) apply simp
  apply(case_tac "n") apply simp+
done

lemma list_updates_n_neq [simp]: "j < i \<or> j \<ge> i + n \<Longrightarrow> (list_updates_n l i n v)!j = l!j"
  apply(induct l arbitrary: i j n v) apply simp
    apply(case_tac "i") apply(case_tac "n") apply simp+
    apply(case_tac "n") apply simp apply(case_tac "j") apply simp apply auto
done

lemma list_updates_n_beyond[simp]: "i \<ge> length l \<Longrightarrow> (list_updates_n l i n v) = l"
  apply(induct l arbitrary: i n v)
    apply simp apply(case_tac "i") by auto

(* move the lemma to ``List_aux.thy'' *)
lemma lst_udptn_set_eq: "n > 0 \<Longrightarrow> list_updates_n (lst[jj := TAG]) (jj div n * n) n TAG1 =
    list_updates_n lst (jj div n * n) n TAG1"
apply(rule nth_equalityI) apply simp
apply clarify 
apply(case_tac "i = jj") 
  apply(subgoal_tac "i \<ge> jj div n * n") prefer 2 apply (metis divn_mult_n less_or_eq_imp_le)
  apply(subgoal_tac "i < jj div n * n + n") prefer 2
  apply (metis (no_types) add.commute dividend_less_div_times)
  apply simp 
  by (metis length_list_update length_list_update_n list_updates_n_eq list_updates_n_neq not_less nth_list_update_neq)


(* should be moved to list_aux.thy *)
thm list_updates_n.simps
lemma list_updates_n_simps2: "list_updates_n (a#lst) (Suc ii) m v = a # list_updates_n lst ii m v"
by fastforce

lemma list_updates_n_simps2': "ii > 0 \<Longrightarrow> list_updates_n (a#lst) ii m v = a # list_updates_n lst (ii - 1) m v"
using list_updates_n_simps2[of a lst "ii - 1" m v] by force

lemma lst_updt1_eq_upd: "list_updates_n lst ii 1 v = lst[ii := v]"
  apply(induct lst arbitrary: ii) apply simp
  apply(case_tac "ii = 0") apply simp
    using list_updates_n_simps2'
    by (metis One_nat_def Suc_pred list_update_code(3) neq0_conv) 

lemma list_neq_udpt_neq: 
"\<forall>i<length l. l ! i \<noteq> P \<Longrightarrow>
 l' = list_updates_n l s n Q \<Longrightarrow>
 P \<noteq> Q \<Longrightarrow> 
 \<forall>i<length l'. l' ! i \<noteq> P"
apply(induct l' arbitrary:l) apply simp
  by (metis le_neq_implies_less length_list_update_n list_updates_n_eq list_updates_n_neq nat_le_linear)


lemma lst_updts_eq_updts_updt: 
"1 \<le> ii \<Longrightarrow>
  list_updates_n lst st (ii - 1) TAG [st + ii - 1 := TAG] =
  list_updates_n lst st ii TAG"
apply(rule nth_equalityI)
  apply simp
  apply clarsimp apply(rename_tac "ia")
    apply(case_tac "ia < st") using list_updates_n_neq apply simp
    apply(case_tac "ia \<ge> st + ii") using list_updates_n_neq apply simp
    apply(case_tac "ia < st + ii - 1") using list_updates_n_eq apply simp
    apply(subgoal_tac "ia = st + ii - 1") prefer 2
      apply force
    apply(subgoal_tac "length lst = length (list_updates_n lst st ii TAG)")
      prefer 2 apply simp
    apply(subgoal_tac "length lst = length (list_updates_n lst st (ii - 1) TAG)")
      prefer 2 using length_list_update_n apply metis
    apply(case_tac "ia \<ge> length lst") apply linarith
      apply(subgoal_tac "list_updates_n lst st (ii - 1) TAG [st + ii - 1 := TAG] ! ia = TAG") prefer 2
        apply (metis nth_list_update_eq) 
      apply(subgoal_tac " list_updates_n lst st ii TAG ! ia = TAG") prefer 2
        apply (meson list_updates_n_eq not_less)
  using One_nat_def by presburger


primrec removes :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where "removes [] l = l" |
      "removes (x#xs) l = removes xs (remove1 x l)"

lemma removes_distinct [simp]: "distinct l \<Longrightarrow> distinct (removes rs l)"
  apply(induct rs arbitrary:l) by auto

lemma removes_length [simp]: "\<lbrakk>set rs \<subseteq> set l; distinct l; distinct rs \<rbrakk> 
        \<Longrightarrow> length rs + length (removes rs l) = length l"
  apply(induct rs arbitrary:l)
    apply simp apply auto
  by (metis (no_types, lifting) One_nat_def Suc_pred distinct_remove1 
        in_set_remove1 length_pos_if_in_set length_remove1 subset_eq)

lemma removes_empty [simp]: "removes rs [] = []"
  apply(induct rs) by simp+

lemma removes_subs1 [simp]: "set (removes rs l) \<subseteq> set l"
  apply(induct rs arbitrary: l) apply simp apply simp
  apply(subgoal_tac "set (remove1 a l) \<subseteq> set l") apply auto[1]
  by (simp add: set_remove1_subset)
  
lemma removes_subs2 [simp]: "distinct l \<Longrightarrow> set (removes (a#rs) l) \<subseteq> set (removes rs l)"
  apply simp 
  apply(induct rs arbitrary: l a) 
    apply auto by (metis (full_types) distinct_remove1 remove1_commute set_mp) 
    
lemma removes_nin [simp]: "\<lbrakk>x \<in> set rs; distinct l\<rbrakk> \<Longrightarrow> x \<notin> set (removes rs l)"
  apply(induct rs arbitrary:l x)
    apply simp 
    apply simp apply auto
  by (metis DiffE contra_subsetD removes_subs1 set_remove1_eq singletonI) 


lemma rmvs_empty: "a \<in> set es \<Longrightarrow> removes es [a] = []"
apply(induct es) apply simp apply auto
done

lemma rmvs_unchg: "a \<notin> set es \<Longrightarrow> removes es [a] = [a]"
apply(induct es) apply simp apply auto
done

lemma rmvs_onemore_same: 
"distinct lst \<Longrightarrow> e \<notin> set lst \<Longrightarrow> removes (es@[e]) lst = removes es lst"
apply(induct es arbitrary:lst) 
apply (simp add: remove1_idem)
apply auto
done

lemma rmvs_rev: "removes (es@[e]) lst = remove1 e (removes es lst)"
apply(induct es arbitrary:lst) apply simp apply auto
done

definition "inserts xs l \<equiv> l @ xs"

lemma inserts_set_un: "set (inserts xs l) = set xs \<union> set l"
  by (simp add: inserts_def sup_commute)

lemma inserts_emp1: "set (inserts xs []) = set xs"
  using inserts_set_un[of xs "[]"] by auto

lemma inserts_emp2: "set (inserts [] l) = set l"
  using inserts_set_un[of "[]" l] by auto


lemma list_updt_samelen: "length l = length (l[jj := a])" by simp

lemma list_nhd_in_tl_set: "el \<in> set l \<Longrightarrow> el \<noteq> hd l \<Longrightarrow> el \<in> set (tl l)"
  by (metis empty_iff empty_set list.exhaust_sel set_ConsD) 

lemma dist_hd_nin_tl: "distinct l \<Longrightarrow> a\<in>set (tl l) \<Longrightarrow> a \<noteq> hd l"
  by (metis distinct.simps(2) equals0D list.collapse set_empty tl_Nil) 



end