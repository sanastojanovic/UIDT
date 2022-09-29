theory mi18467_Milana_Novakovic

imports Complex_Main
begin
  (*N4 teorema 
izvor:
https://www.imo-official.org/problems/IMO2009SL.pdf
Solution 1
*)

(*Za n=4 vazi, to pokazujemo primerom, tako da vazi i za sve manje od 4 *)

lemma
  assumes "(a1::real) = 4" "(a2::real) = 33" "(a3::real) = 217" "(a4::real) = 1384"       
  shows "a3 + 1 = (a2\<^sup>2 + 1) / (a1 + 1)"
proof-
  have pomoc1: "a2\<^sup>2 + 1 = 1090" using assms(2) by auto
  also have "(a2\<^sup>2 + 1) / (a1 + 1) = 218" using pomoc1 and assms(1) by auto
  then show "a3 + 1 =(a2\<^sup>2 + 1) / (a1 + 1)  " using assms(3) by auto
qed


lemma pomoc_mod:
  fixes x::nat
  fixes m::nat
  assumes "x mod 2 = 1"
  shows " x= 2*m+1"
  using assms
  sorry

(*nije bilo potrebno na kraju*)

lemma mod_4: 
  fixes x::nat
  fixes m::nat
  assumes "x mod 2 \<noteq> 0"
  shows"x\<^sup>2 mod 4 = 1"
proof-
  have "x= 2*m+1" using assms(1) pomoc_mod by auto
  then have "x\<^sup>2 = (2*m+1)\<^sup>2" by auto
  then have "x\<^sup>2 -1 = (2*m +1)\<^sup>2 -1" by auto
 then have "x\<^sup>2 -1 = 4*m\<^sup>2 + 4*m +1 -1" 
   by (simp add: \<open>x\<^sup>2 - 1 = (2 * m + 1)\<^sup>2 - 1\<close> \<open>x = 2 * m + 1\<close> ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1) add_mult_distrib add_mult_distrib2 nat_mult_1 power2_eq_square)
  then have "x\<^sup>2 -1 = 4*(m\<^sup>2 + m)" by auto
 then have "x\<^sup>2 = 4*(m\<^sup>2 + m) + 1" 
   by (simp add: \<open>x = 2 * m + 1\<close> power2_eq_square)
  then show "x\<^sup>2 mod 4 = 1" 
    by simp
qed





(*Dokazujemo da za n=5 ne radi*)
lemma "a1 je parno":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0"
  assumes "a2\<^sup>2 +1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  shows  "(a1 mod 2) =  0"
proof (rule ccontr)
  assume "(a1 mod 2) \<noteq>  0"
  then have pomoc1:"(a1 + 1) mod 2 = 0"
    by (metis add_self_mod_2 mod_add_right_eq not_mod_2_eq_0_eq_1)
  then have pomoc2:"(a2\<^sup>2 +1) mod 2 = 0" using assms(4) and pomoc1
    using bits_mod_0 by fastforce
  then have pomoc3: "a2\<^sup>2 mod 2 = 1" using pomoc2 
    by presburger
  then have pomoc4:"a2 mod 2 \<noteq> 0"
    by (metis bits_mod_0 not_mod_2_eq_1_eq_0 power_mod zero_eq_power2)
  then have pomoc5: "a2\<^sup>2 mod 4 =1" 
    by (metis bits_one_mod_two_eq_one less_exp mod_less mult_2 mult_2_right nat_mult_less_cancel_disj numeral_Bit0 numeral_One pomoc3 pomoc_mod power2_eq_square power4_eq_xxxx)
  then have "a3 mod 2 =0" using pomoc5 pomoc2 pomoc1
    by (metis add_cancel_right_left add_self_div_2 cong_exp_iff_simps(8) mult_2 not_mod_2_eq_0_eq_1 pomoc_mod)
  then have pomoc6:  "(a3\<^sup>2 + 1) mod 2 = 1" 
    by (metis add_cancel_right_left bits_mod_0 bits_one_mod_two_eq_one mod_add_left_eq power_mod zero_power2)
  then have  "(a2 + 1) dvd (a3\<^sup>2 + 1) " using assms(5) 
    using dvdI by blast
  then show False using pomoc6 pomoc3 
    by (metis assms(5) even_mult_iff even_plus_one_iff pomoc_mod power2_eq_square)
qed

    
lemma "a2 je parno":
  assumes "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"
  shows "(a2 mod 2) =  0"
proof (rule ccontr)
  assume "(a2 mod 2) \<noteq>  0"
   then have pomoc1:"(a2 + 1) mod 2 = 0"
    by (metis add_self_mod_2 mod_add_right_eq not_mod_2_eq_0_eq_1)
  then have pomoc2:"(a3\<^sup>2 +1) mod 2 = 0" using assms(4) and pomoc1
    using bits_mod_0 by fastforce
then have pomoc3: "a3\<^sup>2 mod 2 = 1" using pomoc2 
  by presburger
then have pomoc4:"a3 mod 2 \<noteq> 0"
  by (metis bits_mod_0 not_mod_2_eq_1_eq_0 power_mod zero_eq_power2)
 then have pomoc5: "a3\<^sup>2 mod 4 =1" 
    by (metis bits_one_mod_two_eq_one less_exp mod_less mult_2 mult_2_right nat_mult_less_cancel_disj numeral_Bit0 numeral_One pomoc3 pomoc_mod power2_eq_square power4_eq_xxxx)
 then have "a4 mod 2 =0" using pomoc5 pomoc2 pomoc1
    by (metis add_cancel_right_left add_self_div_2 cong_exp_iff_simps(8) mult_2 not_mod_2_eq_0_eq_1 pomoc_mod)
  then have pomoc6:  "(a4\<^sup>2 + 1) mod 2 = 1" 
    by (metis add_cancel_right_left bits_mod_0 bits_one_mod_two_eq_one mod_add_left_eq power_mod zero_power2)
  then have  "(a3 + 1) dvd (a4\<^sup>2 + 1) " using assms(5) 
    using dvdI by blast
  then show False using pomoc6 pomoc3 
      by (metis assms(5) even_mult_iff even_plus_one_iff pomoc_mod power2_eq_square)
qed

lemma "a3 je parno":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows "a3 mod 2 = 0"
proof-
  have pomoc1:"(a3 + 1) dvd (a2\<^sup>2 + 1)" using assms(6)
    by (metis dvd_triv_right)
  then have "(a2\<^sup>2 + 1) mod 2 \<noteq> 0" using "a2 je parno" 
    by (metis assms(2) assms(3) assms(4) assms(7) assms(8) even_mod_2_iff even_plus_one_iff even_power zero_less_numeral)
  then have "(a3 + 1) mod 2 \<noteq> 0" using pomoc1 
    by (metis assms(6) even_mult_iff mod2_eq_if)  
  then show "a3 mod 2 = 0" 
    by (metis add_self_mod_2 mod_add_right_eq not_mod_2_eq_1_eq_0)
qed
 

lemma "a4 je parno":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows "a4 mod 2 = 0"
proof-
  have pomoc1:"(a4 + 1) dvd (a3\<^sup>2 + 1)" using assms(7)
    by (metis dvd_triv_right) 
  then have "(a3\<^sup>2 + 1) mod 2 \<noteq> 0" using "a3 je parno" 
    by (metis "a1 je parno" assms(2) assms(3) assms(4) assms(6) assms(7) assms(8) even_mult_iff even_plus_one_iff mod_0_imp_dvd mult.commute)
  then have "(a4 + 1) mod 2 \<noteq> 0" using pomoc1
    by (metis assms(7) even_mult_iff mod2_eq_if)
  then show "a4 mod 2 = 0" 
    by (metis add_self_mod_2 mod_add_right_eq not_mod_2_eq_1_eq_0)
qed


lemma "a5 je parno":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows "a5 mod 2 = 0"
proof-
  have pomoc1: "(a5 + 1) dvd (a4\<^sup>2 + 1)" using assms(8)
    by (metis dvd_triv_right)
  then have "(a4\<^sup>2 + 1) mod 2 \<noteq> 0" using "a4 je parno" 
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) bits_one_mod_two_eq_one even_add even_power less_numeral_extra(1) mod_greater_zero_iff_not_dvd zero_less_numeral)
  then have "(a5 + 1) mod 2 \<noteq> 0" using pomoc1 
    by (metis assms(8) even_mult_iff mod2_eq_if)
  then show "a5 mod 2 = 0" 
    by (metis add_self_mod_2 mod_add_right_eq not_mod_2_eq_1_eq_0)
qed


lemma "viet_sabiranje":
  fixes x1::nat
  fixes x2::nat
  fixes a1::nat
  assumes "(x::nat) >0"
  assumes "x\<^sup>2 + a1*x + a0 = 0"
  assumes "x1\<^sup>2 + a1*x1 + a0 = 0"
  assumes "x2\<^sup>2 + a1*x2 + a0 = 0"
  assumes "a1 > 0"
  shows "x1 + x2 = -a1"
proof-
  have pomoc1:"x\<^sup>2 + a1*x + a0 = (x-x1)*(x-x2)" using assms(1) assms(2) assms(3) assms(4) 
    using add.right_neutral by force
  then have "(x-x1)*(x-x2) = x\<^sup>2 - x*x2 - x*x1 + x1*x2" 
    using add_is_0 assms(2) assms(4) diff_0_eq_0 mult_0_right power_not_zero by auto
  also have " ... =  x\<^sup>2 - x*(x2 + x1) + x1*x2" 
    using add_mult_distrib2 diff_diff_left by presburger
  then have "a1= - (x2+x1)" using pomoc1 
    using assms(1) assms(2) by force
  then show "x1+x2 =- a1" by auto
qed



lemma "viet_mnozenje":
  fixes x1::nat
  fixes x2::nat
  fixes a1::nat
  assumes "(x::nat) >0"
  assumes "x\<^sup>2 + a1*x + a0 = 0"
  assumes "x1\<^sup>2 + a1*x1 + a0 = 0"
  assumes "x2\<^sup>2 + a1*x2 + a0 = 0"
  assumes "a1 > 0"
  shows "x1 * x2 = a0"
proof-
 have pomoc1:"x\<^sup>2 + a1*x + a0 = (x-x1)*(x-x2)" using assms(1) assms(2) assms(3) assms(4) 
    using add.right_neutral by force
  then have "(x-x1)*(x-x2) = x\<^sup>2 - x*x2 - x*x1 + x1*x2" 
    using add_is_0 assms(2) assms(4) diff_0_eq_0 mult_0_right power_not_zero by auto
  also have " ... =  x\<^sup>2 - x*(x2 + x1) + x1*x2" 
    using add_mult_distrib2 diff_diff_left by presburger
 then show "x1*x2=a0" using pomoc1
   using assms(2) calculation by fastforce 
qed


lemma "jednacina nema resenje":
  assumes "(x1 ::nat) > 0" "(y1::nat) > 0" "(x2::nat) > 0" "(y2::nat) > 0" 
  assumes "x1 mod 2 = 0" "y1 mod 2 = 0" "x2 mod 2 = 0" "y2 mod 2 = 0"
  assumes "a1 = - k*(y1 + 1)"
  assumes "a0 = y1\<^sup>2 - k*(y1 + 1)"
  assumes "x\<^sup>2  + a1*x + a0 = 0"
  assumes "x1\<^sup>2 + a1*x1 + a0 = 0"
  assumes "x2\<^sup>2 + a1*x2 + a0 = 0"
  assumes "x1 \<ge>  y1"
  assumes "x2 \<ge>  y2"
  assumes "x2 + y2 >  x1 + y1"
  assumes "y2 = y1"
  shows False
proof-
  have "x1 + x2 = -a1" using assms(9) assms(10) assms(11) assms(12) assms(13) "viet_sabiranje" 
    by (metis assms(3) not_gr_zero zero_eq_add_iff_both_eq_0 zero_eq_power2)
  then have pomoc1: " x1 + x2 =k*(y1 + 1)" using assms(9) 
    using assms(1) of_nat_0_less_iff by linarith
  have "x1 * x2 = a0" using assms(9) assms(10) assms(11) assms(12) assms(13) "viet_mnozenje" 
    using \<open>int (x1 + x2) = - int a1\<close> add.inverse_neutral mult_less_cancel2 not_gr_zero of_nat_eq_0_iff zero_eq_add_iff_both_eq_0 by fastforce
  then have pomoc2: "x1 * x2 = y1\<^sup>2 - k*(y1 + 1)" using assms(10) 
    by blast
  have "(x1 + 1)*(x2 + 1) =  x1 * x2 + x1 +x2 + 1 " by auto
  then have "(x1 + 1)*(x2 + 1) =y1\<^sup>2 +1" using pomoc1 pomoc2 
    by (metis add_is_0 assms(13) assms(3) gr_implies_not_zero zero_eq_power2)
  then have "(x2 + 1) = (y1\<^sup>2 +1) / (x1 + 1)"
    using assms(12) by auto
  also have "... \<le> (y1\<^sup>2 +1) / (y1 + 1)" using assms(14) 
    by (metis \<open>x1 * x2 = a0\<close> add_is_0 assms(1) assms(13) assms(3) less_not_refl2 mult_is_0) 
  also have "... \<le> y1" 
    using assms(1) assms(12) by auto
  also have "... \<le> x1" using assms(14) by auto
  then have "x2+1 \<le> x1" 
    using calculation by linarith
  then have "x2\<le>x1" 
    by simp
  then have "x2+y2\<le>x1+y1"
    using assms(17) by auto
  then show False using assms(16) by auto
qed

lemma "glavna":
  assumes "(a1::nat) > 0" "(a2::nat) > 0" "(a3::nat) > 0" "(a4::nat) > 0" "(a5::nat) > 0"
  assumes "a2\<^sup>2 + 1 = (a1 + 1)*(a3 + 1)"
  assumes "a3\<^sup>2 + 1 = (a2 + 1)*(a4 + 1)"
  assumes "a4\<^sup>2 + 1 = (a3 + 1)*(a5 + 1)"  
  shows False
  sorry


end
