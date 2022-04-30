theory aux_lemma
imports Main
begin

lemma mod_div_self: "(a::nat) mod b = 0 \<Longrightarrow> (a div b) * b = a"
by auto

lemma mod_div_mult: "(a::nat) mod b = 0 \<Longrightarrow> a div b \<le> (c - 1) \<Longrightarrow> a \<le> c * b - b" 
  apply(subgoal_tac "a \<le> (c - 1) * b")
  apply (simp add: left_diff_distrib')
  by fastforce 

lemma mod0_div_self: "(a::nat) mod b = 0 \<Longrightarrow> b * (a div b) = a" by auto

lemma m_mod_div: "n mod x = 0 \<Longrightarrow> (m::nat) * n div x = m * (n div x)" 
  by auto

lemma pow_mod_0: "x \<ge> y \<Longrightarrow> (m::nat) ^ x mod m ^ y = 0"
  by (simp add: le_imp_power_dvd)

lemma ge_pow_mod_0: "(x::nat) > y \<Longrightarrow> 4 * n * (4::nat) ^ x mod 4 ^ y = 0"
  by (metis less_imp_le_nat mod_mod_trivial mod_mult_right_eq mult_0_right pow_mod_0)


lemma div2_eq_minus: "x \<noteq> 0 \<and> m \<ge> n \<Longrightarrow> (x::nat) ^ m div x ^ n = x ^ (m - n)"
  by (metis add_diff_cancel_left' div_mult_self1_is_m gr0I le_Suc_ex power_add power_not_zero) 

lemma pow_lt_mod0: "(n::nat) > 0 \<and> (x::nat) > y \<Longrightarrow> (n ^ x div n ^ y) mod n = 0"
  by (simp add: div2_eq_minus) 
  
lemma mod_div_gt:
"(m::nat) < n \<Longrightarrow> n mod x = 0 \<Longrightarrow> m div x < n div x"
  by (simp add: less_mult_imp_div_less mod_div_self)

lemma div2_eq_divmul: "(a::nat) div b div c = a div (b * c)"
  by (simp add: Divides.div_mult2_eq) 

lemma addr_in_div: 
"(addr::nat) \<in> {j2 * M ..< (Suc j2) * M} \<Longrightarrow> addr div M = j2"
  by (simp add: div_nat_eqI mult.commute)

lemma divn_mult_n: "x > 0 \<Longrightarrow> (n::nat) = m div x * x \<Longrightarrow> (if m mod x = 0 then m = n else n < m \<and> m < n + x \<and> n mod x = 0)"
  apply auto
  apply (metis div_mult_mod_eq less_add_same_cancel1)
  by (metis add_le_cancel_left div_mult_mod_eq mod_less_divisor not_less)

lemma mod_minus_0: 
"(m::nat) \<le> n \<and> 0 < m  \<Longrightarrow> a * (4::nat) ^ n mod 4 ^ (n - m) = 0"
by (metis diff_le_self mod_mult_right_eq mod_mult_self2_is_0 mult_0 mult_0_right pow_mod_0)

lemma mod_minus_div_4: 
"(m::nat) \<le> n \<and> 0 < m  \<Longrightarrow> a * (4::nat) ^ n div 4 ^ (n - m) mod 4 = 0"
by (metis add.left_neutral add_lessD1 diff_less m_mod_div mod_0 mod_mult_right_eq 
  mult_0_right nat_less_le pow_lt_mod0 pow_mod_0 zero_less_numeral)
    
lemma modn0_xy_n: "(n::nat) > 0 \<Longrightarrow> x mod n = 0 \<Longrightarrow> y mod n = 0 \<Longrightarrow> x < y \<Longrightarrow> x + n \<le> y"
  by (metis Nat.le_diff_conv2 add.commute add.left_neutral add_diff_cancel_left' 
     le_less less_imp_add_positive mod_add_left_eq mod_less not_less)

lemma divn_multn_addn_le: "(n::nat) > 0 \<Longrightarrow> y mod n = 0 \<Longrightarrow> x < y \<Longrightarrow> x div n * n + n \<le> y"
  using divn_mult_n[of n "x div n * n" x] modn0_xy_n
  apply(case_tac "x mod n = 0") 
    apply(rule subst[where s="x" and t="x div n * n"])  apply metis        
    by auto
     

lemma div_in_suc: "y > 0 \<Longrightarrow> n = (x::nat) div y \<Longrightarrow> x \<in> {n * y ..< Suc n * y}"
  by (simp add: dividend_less_div_times) 

lemma int1_eq:"P \<inter> {V} \<noteq> {} \<Longrightarrow> P \<inter> {V} = {V}" by auto

lemma int1_belong: "P \<inter> {V} = {V} \<Longrightarrow> V\<in>P" by auto

lemma two_int_one: "P \<inter> {V} \<inter> {Va} \<noteq> {} \<Longrightarrow> V = Va \<and> {V} = P \<inter> {V} \<inter> {Va}" by auto


end