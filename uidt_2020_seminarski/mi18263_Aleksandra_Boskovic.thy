theory mi18263_Aleksandra_Boskovic 
  imports HOL.Real Main 
begin

(*
lemma kvadrat:
  fixes a :: real
  shows "a*a=a^2"
  by (rule HOL.no_atp(121))

lemma sta_god4 [simp]:
  fixes n :: nat
  assumes "n mod 2 = 0"
  shows "n = 2 * n div 2"
  using assms
  by auto


lemma sta_god2 [simp]:
  fixes n::nat and a :: real
  assumes "n mod 2 = 0"
  shows "a^n=(a^2)^(n div 2)"
  using assms
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have " a ^ Suc n = a ^ Suc (2 * n div 2)"
    by auto
  also have "... = a ^ (2)"
  sorry
  then show ?case sorry
qed   

*)

lemma kvadrat_binoma_zbira [simp]:
  fixes a b ::real
  shows "(a+b)^2 = a^2+2*a*b+b^2"
proof-
  have "(a+b)^2=(a+b)*(a+b)"
   by (auto simp add: HOL.no_atp(121))
  also have "... = a *(a+b)+b*(a+b)"
    by( auto simp add :  HOL.no_atp(100))
  also have "... = a*a + a*b + b*a +b*b"
    by( auto simp add :  HOL.no_atp(126))
  also have "... = a^2 + a*b + b*a +b^2"
    by (auto simp add: HOL.no_atp(121))
  also have "... = a^2+2*a*b+b^2"
    by auto
  finally 
  show ?thesis
    by auto
qed

lemma kvadrat_binoma_razlike [simp]:
  fixes a b ::real
  shows "(a-b)^2 = a^2-2*a*b+b^2"
proof-
  have "(a-b)^2=(a-b)*(a-b)"
   by (auto simp add: HOL.no_atp(121))
  also have "... = a*(a-b)- (b*(a-b))"
    by (auto simp add: Groups.algebra_simps(20))
  also have "... = a*a - a*b -(b*a - b*b)"
    by( auto simp add : Groups.algebra_simps(19))
  also have "... = a^2 - a*b - b*a +b^2"
    by (auto simp add: HOL.no_atp(121))
  also have "... = a^2-2*a*b+b^2"
    by auto
  finally 
  show ?thesis
    by auto
qed

lemma na_4 [simp]:
 fixes a:: real
  shows "a^4 =(a^2)^2"
  by auto

lemma trinom_skalar [simp] :
  fixes a b c d:: real
  shows "(a-b+d)*c = a*c-b*c+d*c"
  by (metis distrib_left minus_real_def mult.commute mult_minus_right)

lemma minus_ispred [simp]:
  fixes  a b c d:: real 
  shows "-(a-b+d) = -a+b-d"
  by simp

lemma proizvod_stepena [simp]:
 fixes a :: real and m n ::nat
 shows "a^n*a^m = a^(m+n)"
  by (simp add: power_add)


lemma bin_5 [simp]:
 fixes a b c d:: real
 shows "(a-b+c)*(a-b+c) = (a-b+c)*a-(a-b+c)*b+(a-b+c)*c"
  by (metis distrib_right minus_real_def mult.commute mult_minus_right)

lemma skupi [simp]:
 fixes a b c d:: real
 shows "a*c + a*d = a*(c+d)"
  by (simp add: ring_class.ring_distribs(1))

lemma oduzmi [simp]:
 fixes a b c d:: real
 shows "a*c - a*d = a*(c-d)"
  by (simp add: right_diff_distrib)


lemma mnozenje_trinoma [simp]:
 fixes a b c d:: real
 shows "(a-b+c)*(a-b+c) = a*a-b*a+c*a-(a*b-b*b+c*b)+(a*c-b*c+c*c)"
  by (simp add: distrib_left right_diff_distrib')

find_theorems "(_ - _) ^ 2"

lemma binom_na_4 :
  fixes a b:: real
  shows "(a-1)^4 =a^4 -4*a^3+ 6*a^2-4*a+1 "
proof-
  have "(a-1)^4 = ((a-1)^2)^2"
    by (rule na_4)
  also have "... = ((a-1)^2)*((a-1)^2)"
    by (simp add: power2_eq_square)
  also have "... = (a^2-2*a*1+1^2)*(a^2-2*a*1+1^2)"
    by auto
  also have "... =  (a^2-(2*a)+1)*(a^2-(2*a)+1)"
    by auto
  also have "... = (a^2-2*a+1)*(a^2)-(a^2-2*a+1)*(2*a)+(a^2-2*a+1)*1"
    using bin_5 by blast
  also have "... =(a^2*a^2-(2*a)*a^2+1*a^2)-(a^2*(2*a)-2*a*(2*a)+1*(2*a))+(a^2*1-(2*a)*1+1*1)"
    using trinom_skalar by presburger
  also have "... =(a^2*a^2-2*a*a^2+1*a^2)-(a^2*2*a-2*a*2*a+1*2*a)+(a^2*1-2*a*1+1*1)"
    by linarith
  also have "... = (a^2*a^2-2*a*a^2+a^2)-(a^2*2*a-4*a*a+2*a)+(a^2-2*a+1)"
    by linarith
  also have "... = (a^2*a^2-2*a*a^2+a^2)-(a^2*2*a-4*a^2+2*a)+(a^2-2*a+1)"
    by (metis (no_types, hide_lams) mult.commute mult.left_commute HOL.no_atp(121))
  also have "... = (a^2*a^2-2*a^1*a^2+a^2)-(a^2*2*a^1-4*a^2+2*a^1)+(a^2-2*a^1+1)"
    by (metis power_one_right)
  also have "... = ((a^2*a^2)-2*(a^1*a^2)+a^2)-((a^1*a^2)*2-4*a^2+2*a^1)+(a^2-2*a^1+1)"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute)
  also have "... = (a^(2+2)-2*a^(1+2)+a^2)-(a^(1+2)*2-4*a^2+2*a^1)+(a^2-2*a^1+1)"
    by (metis power_add)
  also have "... =  (a^4-2*a^3+a^2)-(a^3*2-4*a^2+2*a^1)+(a^2-2*a^1+1)" 
    by (metis eval_nat_numeral(3) numeral_Bit0 plus_1_eq_Suc)
  also have "... =a^4-2*a^3+a^2-a^3*2+4*a^2-2*a^1+a^2-2*a^1+1"
    by linarith
  also have "... = a^4-2*a^3-a^3*2+a^2+4*a^2+a^2-2*a^1-2*a^1+1"
    by linarith
  finally show "(a-1)^4 =a^4 -4*a^3+ 6*a^2-4*a+1"
    by (smt power_one_right)
qed



lemma seminarski_pomocna:
 fixes a b c d :: real
  assumes "a + b +c + d = 6"
  assumes "a^2 + b^2 +c^2 + d^2 =12"
  shows "-((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+6*(a^2+b^2+c^2+d^2)-4*(a+b+c+d)+4 = 
                                    4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)"
proof-
  have "-((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+6*(a^2+b^2+c^2+d^2)-4*(a+b+c+d)+4 
= -((a^4 -4*a^3+ 6*a^2-4*a+1)+(b^4 -4*b^3+ 6*b^2-4*b+1)+(c^4 -4*c^3+ 6*c^2-4*c+1)+
(d^4 -4*d^3+ 6*d^2-4*d+1))+6*(a^2+b^2+c^2+d^2)-4*(a+b+c+d)+4 "
    using binom_na_4 by presburger
  also have "... = -(a^4) +4*a^3- 6*a^2+4*a-1-(b^4) +4*b^3- 6*b^2+4*b-1-(c^4) +4*c^3- 6*c^2+4*c-1-(d^4) +4*d^3- 6*d^2+4*d-1+6*(a^2+b^2+c^2+d^2)-4*(a+b+c+d)+4"
    by linarith
  also have "... = -(a^4) +4*a^3- 6*a^2+4*a-1-(b^4) +4*b^3- 6*b^2+4*b-1-(c^4) +4*c^3- 6*c^2+4*c-1-(d^4) +4*d^3- 6*d^2+4*d-1+6*a^2+6*b^2+6*c^2+6*d^2-4*a-4*b-4*c-4*d+4"
    by smt
  finally show  "-((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+6*(a^2+b^2+c^2+d^2)-4*(a+b+c+d)+4 = 
                                    4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)"
    by smt
qed


lemma seminarski_pomocna_2:
  fixes a b c d :: real
  assumes "a + b +c + d = 6"
  assumes "a^2 + b^2 +c^2 + d^2 =12"
  shows " 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4) = -((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+52 "
  using assms
proof-
  have " 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4) = 
         -((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+6*(a^2+b^2+c^2+d^2)-4*(a+b+c+d)+4"
    using assms(1) assms(2) seminarski_pomocna by presburger
  also have "... =  -((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4) +6*12-4*6+4"
    using assms
    by presburger
  finally show " 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4) = -((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+52 "
    by linarith
qed


lemma pomocna_3:
  fixes a b c d :: int
  assumes "a+1 + b+1 +c+1 + d+1 = 6"
  assumes "(a+1)^2 + (b+1)^2 +(c+1)^2 + (d+1)^2 =12"
  shows "a^4+b^4+c^4+b^4 ≥ ((a^2+b^2+c^2+d^2)^2)/4"
  using assms
  sorry


lemma pomocna_za_3a :
  fixes a b c d :: real
  assumes "a+b +c + d = 6"
  assumes "(a)^2 + (b)^2 +(c)^2 + (d)^2 =12"
 shows "(a-1)^2+(b-1)^2+(c-1)^2+(d-1)^2=4"
proof-
  have "(a-1)^2+(b-1)^2+(c-1)^2+(d-1)^2 = a^2-2*a+1+b^2-2*b+1+c^2-2*c+1+d^2-2*d+1"
    by (auto simp add: Power.comm_ring_1_class.power2_diff)
  also have "... = (a^2+b^2+c^2+d^2)-2*(a+b+c+d)+4"
    by smt
  also have "... = 12 - 2 * 6 + 4"
    by (simp add: assms(1) assms(2))
  finally show "(a-1)^2+(b-1)^2+(c-1)^2+(d-1)^2=4"
    by simp
qed

lemma pomocna_3a:
  fixes a b c d :: real
  assumes "a+b +c + d = 6"
  assumes "(a)^2 + (b)^2 +(c)^2 + (d)^2 =12"
  shows "(a-1)^4+(b-1)^4+(c-1)^4+(d-1)^4 ≥ (((a-1)^2+(b-1)^2+(c-1)^2+(d-1)^2)^2)/4"
  using assms
  sorry
(*
proof-
  have " (((a-1)^2+(b-1)^2+(c-1)^2+(d-1)^2)^2)/4 =(a^2-2*a+1+b^2-2*b+1+c^2-2*c+1+d^2-2*d+1)^2/4 "
    by (smt assms(1) assms(2) pomocna_za_3a)
  also have "... = ((a^2+b^2+c^2+d^2)-2*(a+b+c+d)+4)^2/4"
    by smt
  also have "... = (a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)^2/4"
    sorry
  also have "... = ((a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4))/4"
    by (simp add: power2_eq_square)
 (* also have "... =a^2*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)+b^2*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)+
c^2*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)+d^2*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)-2*a*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)
 -2*b*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)-2*c*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4-2*d*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4)
-4*(a^2+b^2+c^2+d^2-2*a-2*b-2*c-2*d-4))"
    sorry*)
  finally shows "(a-1)^4+(b-1)^4+(c-1)^4+(d-1)^4 ≥ (((a-1)^2+(b-1)^2+(c-1)^2+(d-1)^2)^2)/4"
    sorry
qed

*)
find_theorems "_^2=_*_"

lemma pomocna_4:
 fixes a b c d :: real
 shows "a ≤ b+c ⟷ a-c≤b"
  by linarith

lemma seminarski_dva_zadatak:
  fixes a b c d :: real
  assumes "a + b +c + d = 6"
  assumes "a^2 + b^2 +c^2 + d^2 =12"
  shows "36 ≤ 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)" and " 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4) ≤ 48"
proof-
  have "4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)=-((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)+52 "
    using assms(1) assms(2) seminarski_pomocna_2 by blast
  have "32 ≤ 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4) ⟷ 32-52 ≤ -((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4) "
    using ‹4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) = - ((a - 1) ^ 4 + (b - 1) ^ 4 + (c - 1) ^ 4 + (d - 1) ^ 4) + 52› by linarith
  have "-((a-1)^4 + (b-1)^4 +(c-1)^4 +(d-1)^4)≥(a^4 +b^4 +c^4 +d^4)/4"
   
    sorry
  show  "36 ≤ 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)" and " 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4) ≤ 48"
    sorry
qed




end










