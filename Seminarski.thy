theory Seminarski
  imports Complex_Main Main HOL.NthRoot

begin

primrec proizvod :: "nat \<Rightarrow> real" where
"proizvod 0 = 1" |
"proizvod (Suc n) = ((3*(Suc n) - 2)/(3*(Suc n) - 1)) * proizvod n"

value "proizvod 2"

lemma kubiranje_1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(3*(n+1)-2)^3 = 27*n^3+27*n^2+9*n+1"
proof-
  have "(3*(n+1)-2)^3 = (3*n+3-2)^3"
    by simp
  also have "... = (3*n+1)^3"
    by simp
  also have "... = (3*n+1)^2*(3*n+1)"
    by (simp add: power2_eq_square power3_eq_cube)
  also have "... = (9*n^2+6*n+1)*(3*n+1)"
    by (smt Suc_eq_plus1 eval_nat_numeral(3) mult_2 numeral_Bit0 one_add_one one_power2 plus_1_eq_Suc power2_sum power_mult_distrib semiring_normalization_rules(18) semiring_normalization_rules(25))
  also have "... = (3*n)*(9*n^2+6*n+1)+(9*n^2+6*n+1)"
    by simp
  also have "... = (3*n)*(9*n^2)+(3*n)*(6*n)+(3*n)+(9*n^2+6*n+1)"
    by (simp add: linordered_field_class.sign_simps(18))
  also have "... = (3*9)*(n*n^2)+(3*6)*(n*n)+(3*n)+(9*n^2+6*n+1)"
  by simp
  also have "... = (27)*(n*n^2)+(18)*(n*n)+(3*n)+(9*n^2+6*n+1)"
    by simp
  also have "... = 27*n^3+18*n^2+3*n+9*n^2+6*n+1"
    by (metis (no_types, lifting) One_nat_def numeral_3_eq_3 one_add_one plus_1_eq_Suc power2_eq_square semiring_normalization_rules(25) semiring_normalization_rules(27))
  also have "... = 27*n^3+27*n^2+9*n+1"
  by linarith
  finally show ?thesis .
qed

lemma kubiranje_2[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(3*(n+1)-1)^3 = 27*n^3+54*n^2+36*n+8"
proof-
  have "(3*(n+1)-1)^3 = (3*n+3-1)^3"
    by simp
  also have "... = (3*n+2)^3"
    by simp
  also have "... = (3*n+2)^2*(3*n+2)"
    by (simp add: power2_eq_square power3_eq_cube)
  also have "... = (9*n^2+12*n+4)*(3*n+2)"
  by (smt mult_2 mult_2_right numeral_Bit0 numeral_Bit1 one_add_one one_power2 power2_sum power_mult_distrib semiring_normalization_rules(23) semiring_normalization_rules(8))
  also have "... = (3*n)*(9*n^2+12*n+4)+2*(9*n^2+12*n+4)"
    by simp
  also have "... = (3*n)*(9*n^2)+(3*n)*(12*n)+(3*n)*4+2*(9*n^2+12*n+4)"
    by (simp add: linordered_field_class.sign_simps(18))
  also have "... = (3*9)*(n*n^2)+(3*12)*(n*n)+(12*n)+2*(9*n^2+12*n+4)"
  by simp
  also have "... = (27)*(n*n^2)+(36)*(n*n)+(12*n)+2*(9*n^2+12*n+4)"
  by simp
  also have "... = 27*n^3+36*n^2+12*n+(18*n^2)+(24*n)+8"
  by (simp add: power2_eq_square power3_eq_cube)
  also have "... = 27*n^3+54*n^2+36*n+8"
  by linarith
  finally show ?thesis .
qed

lemma kubiranje_korena1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(root 3 (8*(n+1)))^3=8*(n+1)"
  by simp

lemma kubiranje_korena2[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(root 3 (8*n))^3=8*(n)"
  by simp

lemma zakljucak1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "16*n+8\<ge>0"
  by blast

lemma razlika_3korena1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "((3*(n+1)-2)*(root 3 (8*(n+1))))^3-((3*(n+1)-1)*(root 3 (8 * n)))^3\<ge>0"
proof-
  have  1:"((3*(n+1)-2)*(root 3 (8*(n+1))))^3-((3*(n+1)-1)*(root 3 (8 * n)))^3 = (3*(n+1)-2)^3*(root 3 (8*(n+1)))^3-(3*(n+1)-1)^3*(root 3 (8 * n))^3"
  by (simp add: power_mult_distrib)
  then have 2:"... = (27*n^3+27*n^2+9*n+1)*(root 3 (8*(n+1)))^3-(27*n^3+54*n^2+36*n+8)*(root 3 (8 * n))^3"
    using assms kubiranje_1 kubiranje_2 by auto
  then have 3:"... = (27*n^3+27*n^2+9*n+1)*(8*(n+1))-(27*n^3+54*n^2+36*n+8)*(root 3 (8*n))^3"
    by (metis (no_types, lifting) assms of_nat_mult kubiranje_korena1 kubiranje_korena2)
  then have 4:"... = (27*n^3+27*n^2+9*n+1)*(8*n+8)-(27*n^3+54*n^2+36*n+8)*(root 3 (8*n))^3"   
    by (metis (mono_tags, hide_lams) add.commute mult.assoc mult.commute semiring_normalization_rules(19) semiring_normalization_rules(29) semiring_normalization_rules(3) semiring_normalization_rules(34))
  then have 5:"... = (27*n^3+27*n^2+9*n+1)*(8*n)+(27*n^3+27*n^2+9*n+1)*8-(27*n^3+54*n^2+36*n+8)*(root 3 (8*n))^3" 
    by (simp add: add_mult_distrib2)
  then have 6:"... = (27*n^3)*(8*n)+(27*n^2)*(8*n)+(9*n)*(8*n)+(8*n)+(27*n^3+27*n^2+9*n+1)*8-(27*n^3+54*n^2+36*n+8)*(root 3 (8*n))^3"
    by (simp add: add_mult_distrib)
  then have 7:"... = (27*n^3)*(8*n)+(27*n^2)*(8*n)+(9*n)*(8*n)+(8*n)+27*n^3*8+27*n^2*8+9*n*8+8-(27*n^3+54*n^2+36*n+8)*(root 3 (8*n))^3"  
    by (simp add: add_mult_distrib)
  then have 8:"... = (27*n^3)*(8*n)+(27*n^2)*(8*n)+(9*n)*(8*n)+(8*n)+27*n^3*8+27*n^2*8+9*n*8+8-((27*n^3)*(root 3 (8*n))^3+(54*n^2)*(root 3 (8*n))^3+(36*n)*(root 3 (8*n))^3+8*(root 3 (8*n))^3)"
    using add_mult_distrib 
  by (simp add: semiring_normalization_rules(8))
  then have 9:"... = (27*n^3)*(8*n)+(27*n^2)*(8*n)+(9*n)*(8*n)+(8*n)+27*n^3*8+27*n^2*8+9*n*8+8-(27*n^3)*(root 3 (8*n))^3-(54*n^2)*(root 3 (8*n))^3-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
    by simp
  then have 10:"... = (27*n^2)*(8*n)+(9*n)*(8*n)+(8*n)+27*n^3*8+27*n^2*8+9*n*8+8-(54*n^2)*(root 3 (8*n))^3-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
    by simp
  then have 11:"... = (27*n^2)*(root 3 (8*n))^3+(9*n)*(root 3 (8*n))^3+(root 3 (8*n))^3+27*n^3*8+27*n^2*8+9*n*8+8-(54*n^2)*(root 3 (8*n))^3-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
    by auto
  then have 12:"... = (27*n^2)*(8*n)+(9*n)*(8*n)+(root 3 (8*n))^3+27*n^3*8+27*n^2*8+9*n*8+8-(54*n^2)*(8*n)-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
    by auto
  then have 13:"... = (27*8)*(n^2*n)+(9*8)*(n*n)+(root 3 (8*n))^3+27*8*n^3+27*8*n^2+9*n*8+8-(54*8)*(n^2*n)-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
  by linarith
  then have 14:"... = (216)*(n^3)+(72)*(n^2)+(root 3 (8*n))^3+216*n^3+216*n^2+72*n+8-(432)*(n^3)-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
  by (simp add: power2_eq_square power3_eq_cube)
  then have 15:"... = 432*n^3+288*n^2+(root 3 (8*n))^3+72*n+8-432*n^3-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
    by simp
  then have 16:"... = 288*n^2+(root 3 (8*n))^3+72*n+8-(36*n)*(root 3 (8*n))^3-8*(root 3 (8*n))^3"
    by linarith
  then have 17:"... = 288*n^2+(root 3 ( 8*n))^3+72*n+8-(36*n)*(8*n)-8*(root 3 (8*n))^3"
    by simp
  then have 18:"... = 288*n^2+(root 3 ( 8*n))^3+72*n+8-(36*8)*(n*n)-8*(root 3 (8*n))^3"
    by simp
  then have 19:"... = 288*n^2+(root 3 ( 8*n))^3+72*n+8-288*n^2-8*(root 3 (8*n))^3"
  using power2_eq_square by force
  then have 20:"... =  8*n+72*n+8-8*(8*n)"
    using power2_eq_square by force
    then have 22:"... = 16*n+8"
    by simp
  then have 23:"...\<ge>0"
    using assms zakljucak1
  using of_nat_0_le_iff by blast
  then show ?thesis 
  by (smt "1" "10" "11" "12" "13" "14" "15" "16" "17" "18" "19" "2" "20" "22" "3" "4" "5" "6" "7" "8")
qed

lemma pomocna2[simp]:
  fixes n::nat
  assumes "n>0"
  assumes "((3*(n+1)-2)*(root 3 (8*(n+1))))^3-((3*(n+1)-1)*(root 3 (8 * n)))^3\<ge>0"
  shows "((3*(n+1)-2)*(root 3 (8*(n+1))))^3\<ge>((3*(n+1)-1)*(root 3 (8 * n)))^3"
  using assms
proof-
  have  "((3*(n+1)-2)*(root 3 (8*(n+1))))^3-((3*(n+1)-1)*(root 3 (8 * n)))^3\<ge>0"
    using assms by blast
  then show ?thesis 
    by simp
qed

lemma pomocna3[simp]:
  fixes n::nat
  assumes "n>0"
  assumes "((3*(n+1)-2)*(root 3 (8*(n+1))))^3\<ge>((3*(n+1)-1)*(root 3 (8 * n)))^3"
  shows "(3*(n+1)-2)*(root 3 (8*(n+1)))\<ge>(3*(n+1)-1)*(root 3 (8 * n))"
  using assms
proof-
  have  "((3*(n+1)-2)*(root 3 (8*(n+1))))^3\<ge>((3*(n+1)-1)*(root 3 (8 * n)))^3"
    using assms by blast
  then have "root 3 (((3*(n+1)-2)*(root 3 (8*(n+1))))^3) \<ge>root 3 (((3*(n+1)-1)*(root 3 (8 * n)))^3)"
  using real_root_le_mono zero_less_numeral by blast
  then show ?thesis 
  by (simp add: real_root_power_cancel)
qed

lemma kub_je_veci_od_nule1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "root 3 (8*(n+1))> 0"
  by simp

lemma kub_je_veci_od_nule2[simp]:
  fixes n::nat
  assumes "n>0"
  shows "root 3 (8*n)> 0"
  using assms by auto

lemma veci_od_nule1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(3*(n+1)-1)> 0"
  using assms by auto

lemma medjukorak[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(3*(n+1)-2)\<ge>((3*(n+1)-1)*(root 3 (8 * n)))/(root 3 (8*(n+1)))"
  using assms kub_je_veci_od_nule1
proof-
  have "(3*(n+1)-2)*(root 3 (8*(n+1)))\<ge>(3*(n+1)-1)*(root 3 (8 * n))"
    using assms razlika_3korena1 pomocna3 by auto 
  then have "((3*(n+1)-2)*(root 3 (8*(n+1))))/(root 3 (8*(n+1)))\<ge>((3*(n+1)-1)*(root 3 (8 * n)))/(root 3 (8*(n+1)))"
    by (smt assms divide_right_mono kub_je_veci_od_nule1)
  then have "(3*(n+1)-2)\<ge>((3*(n+1)-1)*(root 3 (8 * n)))/(root 3 (8*(n+1)))"
    using assms(1) by auto
  then show ?thesis
    by (simp add: mult.commute)
qed

lemma kljucan_dokaz_za_levu_stranu[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(3*(n+1)-2)/((3*(n+1)-1)*(root 3 (8 * n)))\<ge>1/(root 3 (8*(n+1)))"
  using assms
proof-
  have "(3*(n+1)-2)\<ge>((3*(n+1)-1)*(root 3 (8 * n)))/(root 3 (8*(n+1)))"
    using assms razlika_3korena1 pomocna3 medjukorak by auto
  then have "(3*(n+1)-2)/(root 3 (8 * n))\<ge>((3*(n+1)-1)*(root 3 (8 * n)))/(root 3 (8*(n+1)))*(1/(root 3 (8 * n)))"
    using kub_je_veci_od_nule2 assms
    by (metis (no_types, hide_lams) divide_right_mono mult.right_neutral of_nat_0_le_iff real_root_pos_pos_le times_divide_eq_right)
  then have "(3*(n+1)-2)/(root 3 (8 * n))\<ge>((3*(n+1)-1))/(root 3 (8*(n+1)))"
    using assms(1) by auto
  then have "((3*(n+1)-2)/(root 3 (8 * n)))*(1/(3*(n+1)-1))\<ge>((3*(n+1)-1))/(root 3 (8*(n+1)))*(1/(3*(n+1)-1))"
    using assms veci_od_nule1 
  by (smt divide_le_0_1_iff division_ring_divide_zero of_nat_0_le_iff real_mult_le_cancel_iff1 times_divide_eq_right)
  then have "((3*(n+1)-2)/(root 3 (8 * n)))*(1/(3*(n+1)-1))\<ge>1/(root 3 (8*(n+1)))"
    by simp
  then show ?thesis
    by (simp add: mult.commute)
qed

lemma pomocna4[simp]:
  fixes n::nat
  assumes "n>0"
  shows "8*(root 3 (7*n+1))^3=8*(7*n+1)"
  by simp

lemma kubiranje_3[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3=(27*n^3+54*n^2+36*n+8)*(7*n+1)"
  by (metis (no_types, lifting) of_nat_0_le_iff of_nat_mult real_root_pow_pos2 zero_less_numeral)

lemma kubiranje_4[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(27*n^3+27*n^2+9*n+1)*(root 3 (7*(n+1)+1))^3=(27*n^3+27*n^2+9*n+1)*(7*(n+1)+1)"
  by (metis (no_types, lifting) of_nat_0_le_iff of_nat_mult real_root_pow_pos2 zero_less_numeral)

lemma p1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "8*(root 3 (7*n+1))^3 =8*( 7*n+1)"
  by simp

lemma p2[simp]:
  fixes n::nat
  assumes "n>0"
  shows "-56*n-8=-8*(7*n+1)"
  by simp

lemma razlika_3korena2[simp]:
  fixes n::nat
  assumes "n>0"
  shows "((3*(n+1)-1)*(root 3 (7*n+1)))^3-((3*(n+1)-2)*(root 3 (7*(n+1)+1)))^3\<ge>0"
proof-
  have  1:"((3*(n+1)-1)*(root 3 (7*n+1)))^3-((3*(n+1)-2)*(root 3 (7*(n+1)+1)))^3 = (3*(n+1)-1)^3*(root 3 (7*n+1))^3-(3*(n+1)-2)^3*(root 3 (7*(n+1)+1))^3"
  by (simp add: power_mult_distrib)
  then have 2:"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-(27*n^3+27*n^2+9*n+1)*(root 3 (7*(n+1)+1))^3"
  using assms kubiranje_1 kubiranje_2 by auto
  then have 3:"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-(27*n^3+27*n^2+9*n+1)*(7*(n+1)+1)"
    by (metis (no_types, lifting) of_nat_0_le_iff of_nat_mult real_root_pow_pos2 zero_less_numeral)
  then have 4:"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-(27*n^3+27*n^2+9*n+1)*(7*n+7+1)"   
  by simp
  then have 5:"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-((27*n^3+27*n^2+9*n+1)*(7*n+1) + 7*(27*n^3+27*n^2+9*n+1))"
    by (simp add: add_mult_distrib2)
  then have "5a":"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-(27*n^3+27*n^2+9*n+1)*(7*n+1) - 7*(27*n^3+27*n^2+9*n+1)"
    by (simp add: add_mult_distrib2)
  then have 6:"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-(27*n^3*(7*n+1)+27*n^2*(7*n+1)+9*n*(7*n+1)+(7*n+1)) - (7*27*n^3+7*27*n^2+7*9*n+7)"
    by (simp add: add_mult_distrib)
  then have 7:"... = (27*n^3+54*n^2+36*n+8)*(root 3 (7*n+1))^3-27*n^3*(7*n+1)-27*n^2*(7*n+1)-9*n*(7*n+1)-(7*n+1) - 189*n^3-189*n^2-63*n-7"  
    by (simp add: add_mult_distrib)
  then have 8:"... =  27*n^3*(root 3 (7*n+1))^3+54*n^2*(root 3 (7*n+1))^3+36*n*(root 3 (7*n+1))^3+8*(root 3 (7*n+1))^3-27*n^3*(7*n+1)-27*n^2*(7*n+1)-9*n*(7*n+1)-(7*n+1) - 189*n^3-189*n^2-63*n-7"
    using add_mult_distrib
  by (simp add: semiring_normalization_rules(8))
  then have "8a":"... =  27*n^3*(7*n+1)+54*n^2*((root 3 (7*n+1))^3)+36*n*(root 3 (7*n+1))^3+8*(root 3 (7*n+1))^3-27*n^3*(7*n+1)-27*n^2*(7*n+1)-9*n*(7*n+1)-(7*n+1) - 189*n^3-189*n^2-63*n-7"
  by (smt of_nat_0_le_iff of_nat_mult real_root_pow_pos2 zero_less_numeral)
  then have 9:"... = 54*n^2*((root 3 (7*n+1))^3)+36*n*(root 3 (7*n+1))^3+8*(root 3 (7*n+1))^3-27*n^2*(7*n+1)-9*n*(7*n+1)-(7*n+1) - 189*n^3-189*n^2-63*n-7"
    by simp
  then have "... = 54*n^2*(7*n+1)+36*n*(root 3 (7*n+1))^3+8*(root 3 (7*n+1))^3-27*n^2*(7*n+1)-9*n*(7*n+1)-(7*n+1) - 189*n^3-189*n^2-63*n-7"
  by (metis (no_types, lifting) of_nat_0_le_iff of_nat_mult real_root_pow_pos2 zero_less_numeral)
  then have "... = 54*n^2*(7*n+1)+36*n*(7*n+1)+8*(root 3 (7*n+1))^3-27*n^2*(7*n+1)-9*n*(7*n+1)-(7*n+1) - 189*n^3-189*n^2-63*n-7"
  by (metis (no_types, lifting) of_nat_0_le_iff of_nat_add of_nat_mult real_root_pow_pos2 zero_less_numeral)
  then have 10:"... = 54*n^2*7*n+54*n^2+36*n*7*n+36*n+8*(root 3 (7*n+1))^3-(27*n^2*7*n+27*n^2)-(9*n*7*n+9*n)-(7*n+1) - 189*n^3-189*n^2-63*n-7"
    by simp
  then have 11:"... =378*n^2*n+54*n^2+252*n*n+36*n+8*(root 3 (7*n+1))^3-189*n^2*n-27*n^2-63*n*n-9*n-7*n-1 - 189*n^3-189*n^2-63*n-7"
    by auto
  then have 12:"...  = 378*n^3+54*n^2+252*n^2+36*n+8*(root 3 (7*n+1))^3-189*n^3-27*n^2-63*n^2-9*n-7*n-1 - 189*n^3-189*n^2-63*n-7"
  by (simp add: power2_eq_square power3_eq_cube)
  then have 13:"... = 54*n^2+252*n^2+36*n+8*(root 3 (7*n+1))^3-27*n^2-63*n^2-9*n-7*n-1 -189*n^2-63*n-7"
    by linarith
  then have 14:"... = 306*n^2+36*n+8*(root 3 (7*n+1))^3-1 -279*n^2-79*n-7"
  by (simp add: power2_eq_square power3_eq_cube)
  then have 15:"... = 306*n^2+36*n+8*(root 3 (7*n+1))^3 -279*n^2-23*n-56*n-8"
  by linarith
  then have 16:"... =306*n^2+36*n+8*(root 3 (7*n+1))^3 -279*n^2-23*n-8*(7*n+1)"
    using p2 by simp
  then have 17:"... =306*n^2+36*n+8*(root 3 (7*n+1))^3 -279*n^2-23*n-8*(root 3 (7*n+1))^3"
  by simp
  then have 18:"... = 306*n^2+36*n-279*n^2-23*n"
    by simp
  then have 19:"... = 27*n^2+13*n"
    by simp
  then have 23:"...\<ge>0"
    using assms zakljucak1
  using of_nat_0_le_iff by blast
  then show ?thesis
  by (smt "1" "10" "11" "12" "13" "14" "15" "16" "17" "18" "19" "2" "3" "4" "5" "5a" "6" "7" "8" "8a" \<open>real (54 * n\<^sup>2 * (7 * n + 1)) + real (36 * n) * root 3 (real (7 * n + 1)) ^ 3 + 8 * root 3 (real (7 * n + 1)) ^ 3 - real (27 * n\<^sup>2 * (7 * n + 1)) - real (9 * n * (7 * n + 1)) - real (7 * n + 1) - real (189 * n ^ 3) - real (189 * n\<^sup>2) - real (63 * n) - 7 = real (54 * n\<^sup>2 * (7 * n + 1) + 36 * n * (7 * n + 1)) + 8 * root 3 (real (7 * n + 1)) ^ 3 - real (27 * n\<^sup>2 * (7 * n + 1)) - real (9 * n * (7 * n + 1)) - real (7 * n + 1) - real (189 * n ^ 3) - real (189 * n\<^sup>2) - real (63 * n) - 7\<close> \<open>real (54 * n\<^sup>2) * root 3 (real (7 * n + 1)) ^ 3 + real (36 * n) * root 3 (real (7 * n + 1)) ^ 3 + 8 * root 3 (real (7 * n + 1)) ^ 3 - real (27 * n\<^sup>2 * (7 * n + 1)) - real (9 * n * (7 * n + 1)) - real (7 * n + 1) - real (189 * n ^ 3) - real (189 * n\<^sup>2) - real (63 * n) - 7 = real (54 * n\<^sup>2 * (7 * n + 1)) + real (36 * n) * root 3 (real (7 * n + 1)) ^ 3 + 8 * root 3 (real (7 * n + 1)) ^ 3 - real (27 * n\<^sup>2 * (7 * n + 1)) - real (9 * n * (7 * n + 1)) - real (7 * n + 1) - real (189 * n ^ 3) - real (189 * n\<^sup>2) - real (63 * n) - 7\<close>)
qed

lemma pomocna5[simp]:
  fixes n::nat
  assumes "n>0"
  shows "((3*(n+1)-1)*(root 3 (7*n+1)))^3\<ge>((3*(n+1)-2)*(root 3 (7*(n+1)+1)))^3"
  using assms 
  using razlika_3korena2 by auto

lemma pomocna6[simp]:
  fixes n::nat
  assumes "n>0"
  shows "(3*(n+1)-1)*(root 3 (7*n+1))\<ge>(3*(n+1)-2)*(root 3 (7*(n+1)+1))"
  using assms 
proof-
  have "((3*(n+1)-1)*(root 3 (7*n+1)))^3\<ge>((3*(n+1)-2)*(root 3 (7*(n+1)+1)))^3"
    using assms razlika_3korena2 by auto
  then have "root 3 (((3*(n+1)-1)*(root 3 (7*n+1)))^3)\<ge>root 3 (((3*(n+1)-2)*(root 3 (7*(n+1)+1)))^3)"
    using assms razlika_3korena2 by auto
  then show ?thesis 
    by (simp add: real_root_power_cancel)
qed

lemma medjukorak1[simp]:
  fixes n::nat
  assumes "n>0"
  shows "((3*(n+1)-1)*(root 3 (7*n+1)))/(root 3 (7*(n+1)+1))\<ge>(3*(n+1)-2)"
  using assms 
proof-
  have "(3*(n+1)-1)*(root 3 (7*n+1))\<ge>(3*(n+1)-2)*(root 3 (7*(n+1)+1))"
    using assms pomocna6 by blast
  then have "((3*(n+1)-1)*(root 3 (7*n+1)))/(root 3 (7*(n+1)+1))\<ge>((3*(n+1)-2)*(root 3 (7*(n+1)+1)))/(root 3 (7*(n+1)+1))"
  by (meson divide_right_mono of_nat_0_le_iff real_root_pos_pos_le)
  thus ?thesis 
  by simp
qed

lemma kubiranje_12[simp]:
  fixes n::nat
  assumes "n>0"
  shows "root 3 (7*n+1)>0"
  by simp

lemma kljucni_korak_za_desnu_stranu[simp]:
  fixes n::nat
  assumes "n>0"
  shows "1/(root 3 (7*(n+1)+1))\<ge>(3*(n+1)-2)/((3*(n+1)-1)*(root 3 (7*n+1)))"
  using assms 
proof-
  have "((3*(n+1)-1)*(root 3 (7*n+1)))/(root 3 (7*(n+1)+1))\<ge>(3*(n+1)-2)"
    using assms medjukorak1 by blast
 then have "((3*(n+1)-1)*(root 3 (7*n+1)))/(root 3 (7*(n+1)+1))*(1/(root 3 (7*n+1)))\<ge>(3*(n+1)-2)*(1/(root 3 (7*n+1)))"
   using kubiranje_12 
  by (smt \<open>real (3 * (n + 1) - 2) \<le> real (3 * (n + 1) - 1) * root 3 (real (7 * n + 1)) / root 3 (real (7 * (n + 1) + 1))\<close> divide_right_mono mult_cancel_left2 of_nat_0_le_iff real_root_pos_pos_le times_divide_eq_right)
 then have "((3*(n+1)-1))/(root 3 (7*(n+1)+1))\<ge>(3*(n+1)-2)*(1/(root 3 (7*n+1)))"
  by simp 
 then have "((3*(n+1)-1))/(root 3 (7*(n+1)+1))*(1/(3*(n+1)-1))\<ge>(3*(n+1)-2)*(1/(root 3 (7*n+1)))*(1/(3*(n+1)-1))"
  by (smt assms divide_le_0_1_iff of_nat_0_less_iff veci_od_nule1 real_mult_le_cancel_iff1)
 then have "1/(root 3 (7*(n+1)+1))\<ge>(3*(n+1)-2)*(1/(root 3 (7*n+1)))*(1/(3*(n+1)-1))"
   by simp
  then show ?thesis 
  by (metis (no_types, hide_lams) divide_divide_eq_left' divide_inverse mult.left_neutral)
qed

theorem desna_strana:
  fixes n::nat
  assumes "n\<ge>1"
  shows "proizvod n \<le> 1/(root 3 (7*n+1))"
  using assms
proof(induction n)
case 0
then show ?case 
  by simp
next
  case (Suc n)
  then have "proizvod (Suc n) = ((3*(Suc n) - 2)/(3*(Suc n) - 1)) *(proizvod n)"
    using proizvod.simps(2) by blast
  then have "... \<le> ((3*(Suc n) - 2)/(3*(Suc n) - 1))*(1/(root 3 (7*n+1)))"
  by (smt Suc.IH division_ring_divide_zero mult_left_mono mult_not_zero neq0_conv of_nat_0 of_nat_0_le_iff proizvod.simps(1) real_of_nat_div4 real_root_zero)
  then show ?case 
  proof-
    have 1:"((3*(Suc n) - 2)/(3*(Suc n) - 1))*(1/(root 3 (7*n+1))) = (3*(Suc n) - 2)/((3*(Suc n) - 1)*(root 3 (7*n+1)))"
      by simp
    then have 2:"... = (3*(n+1) - 2)/((3*(n+1) - 1)*(root 3 (7*n+1)))"
      using Suc_eq_plus1 by presburger
    then have 3:"... \<le> 1/(root 3 (7*(n+1)+1))"
      using kljucni_korak_za_desnu_stranu assms  by fastforce
    then show ?thesis 
    by (smt "1" Suc_eq_plus1 \<open>proizvod (Suc n) = real (3 * Suc n - 2) / real (3 * Suc n - 1) * proizvod n\<close> \<open>real (3 * Suc n - 2) / real (3 * Suc n - 1) * proizvod n \<le> real (3 * Suc n - 2) / real (3 * Suc n - 1) * (1 / root 3 (real (7 * n + 1)))\<close>)
    qed
  qed

theorem leva_strana:
  fixes n::nat
  assumes "n\<ge>1"
  shows "1/(root 3 (8*n)) \<le> proizvod n"
  using assms
proof(induction n)
  case 0
  then show ?case 
  by auto
next
  case (Suc n)
   have "proizvod (Suc n) = ((3*(Suc n) - 2)/(3*(Suc n) - 1)) * (proizvod n)"
        using proizvod.simps(2) by blast
   then have "... \<ge> ((3*(Suc n) - 2)/(3*(Suc n) - 1)) * (1/(root 3 (8*n)))"
     by (smt Suc.IH division_ring_divide_zero mult_left_mono mult_not_zero neq0_conv of_nat_0 of_nat_0_le_iff proizvod.simps(1) real_of_nat_div4 real_root_zero)
   then show ?case
   proof-
     have 1:"((3*(Suc n) - 2)/(3*(Suc n) - 1)) * (1/(root 3 (8*n))) = (3*(Suc n) - 2)/((3*(Suc n) - 1)*(root 3 (8*n)))"
       by auto
     then have 2:"... = (3*(n+1) - 2)/((3*(n+1) - 1)*(root 3 (8*n)))"
       by auto
     then have 3:"(3*(n+1) - 2)/((3*(n+1) - 1)*(root 3 (8*n)))\<ge> 1/(root 3 (8*(n+1)))"
       using assms kljucan_dokaz_za_levu_stranu
       by fastforce
     then have 4:"(3*(Suc n) - 2)/((3*(Suc n) - 1)*(root 3 (8*n)))\<ge> 1/(root 3 (8*(Suc n)))"
     using Suc_eq_plus1 by presburger
     then show ?thesis
     using "1" \<open>proizvod (Suc n) = real (3 * Suc n - 2) / real (3 * Suc n - 1) * proizvod n\<close> \<open>real (3 * Suc n - 2) / real (3 * Suc n - 1) * (1 / root 3 (real (8 * n))) \<le> real (3 * Suc n - 2) / real (3 * Suc n - 1) * proizvod n\<close> by linarith
   qed
 qed

end