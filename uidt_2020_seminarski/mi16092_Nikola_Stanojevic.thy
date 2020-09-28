theory mi16092_Nikola_Stanojevic
  imports Complex_Main 
begin

text\<open>
  Dan 1, zadatak 3 na linku: https://imomath.com/srb/zadaci/2005_mmo.pdf?fbclid=IwAR0mX4Z6RlQIeMVoHAVFrq94rRcz9XrQH4XFwgr7vTFT3TFLBn7BfSU4Iq0

  Neka su x, y i z pozitivni realni brojevi takvi da je x*y*z >= 1.
  Dokazati da je
    (x^5-x^2)/(x^5+y^2+z^2)+(y^5-y^2)/(y^5+z^2+x^2)+(z^5-z^2)/(z^5+x^2+y^2)>=0.
 \<close>

lemma nejednakost:
  fixes x y z::real
  assumes "x > 0" "y > 0" "z > 0" "x * y * z \<ge> 1"
  shows "(x^5 - x^2) / (x^5 + y^2 + z^2) + 
         (y^5 - y^2) / (y^5 + z^2 + x^2) +
         (z^5 - z^2) / (z^5 + x^2 + y^2) \<ge> 0"
  sorry


text\<open>
Drugi seminarski
\<close>

(*Ovaj zadatak je resen uz pomoc resenja koje je bilo dato. 
Bila su dva resenja:
--jedno je ukljucivalo Kosi-Svarcovu ne-je i svodjenje prvobitne ne-je na neku njoj ekvivalentnu i ono je radjeno u malo izmenjenom obliku.
Prvo je dokazano Kosi-Svarcova nejednakost ali ne direktno nego nekim transformacijama i zato su navedene sideLemmas.
Postoje 4 Kosi-Svarcove ne-je, prve 3 prate nejednakosti koje su navedene u resenjima, 4. je navedena jer nisu prolazile neke leme bez nje. 
Takodje su tu i 2 sideLemma koje su modifikacije nekih drugih lema jer Isabelle nije mogao da napravi vezu izmedju pomocnih lema i ono sta tvrdim.
Uz pomoc ovih dokaza uvedena je smena iz jedne u drugu nejednakost (pod pretpostavkom da je drugo resenje vece od 0 ali manje od 3).
Finalna teorema je zadnja i predstavlja resenje zadatka.*)

lemma sideLemma1[simp]:
  fixes a b::real
  assumes "a>0" "b>0"
  shows "a+b\<ge>2*sqrt (a*b)"
  by (smt arith_geo_mean_sqrt assms(1) assms(2) field_sum_of_halves)

lemma sideLemma2[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "2*x^2\<le>x^5+y*z"
proof-
  have "x^5+y*z \<ge> 2*sqrt ((x^5)*(y*z))"
    by (simp add: assms(1))
  then  have "... \<ge>2*(sqrt ((x^4*x)*(y*z)))"
    by (metis (no_types, lifting) numeral_One power_add_numeral2 power_one_right semiring_norm(5) semiring_normalization_rules(18))
  then have "... \<ge> 2*(sqrt ((x^4)*(x*y*z)))"
    by (simp add: mult.assoc)
  then  have "... \<ge> 2*(sqrt (x^4))*(sqrt (x*y*z))"
    by (simp add: real_sqrt_mult)
  then have "... \<ge> 2*(x^2)*(sqrt (x*y*z))"
  by (smt assms(1) numeral_Bit0 power2_eq_square power_add real_sqrt_abs real_sqrt_power)
  then have "... \<ge> 2*(x^2)*(sqrt (1))"
    by (smt assms(1) assms(2) power_not_zero real_mult_le_cancel_iff2 real_sqrt_le_mono zero_le_power)
  then   have "... \<ge> 2*(x^2)"
    by simp 
  then  show ?thesis 
    by blast
qed

lemma sideLemma3[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1"
  shows "x^5+y*z \<ge> 2*sqrt ((x^5)*(y*z))"
  by (simp add: assms(1))

lemma sideLemma4[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(sqrt (x^5*y*z)+y^2+z^2)^2=(x^5)*(y*z)  +2*(sqrt ((x^5)*(y*z)))*(y^2)+2*(sqrt ((x^5)*(y*z)))*(z^2) +(y^4)+2*(y^2)*(z^2)+(z^4)"
proof-
  have "(sqrt (x^5*y*z)+y^2+z^2)^2 = (sqrt (x^5*y*z)+y^2+z^2)*(sqrt (x^5*y*z)+y^2+z^2)"
    by (simp add: power2_eq_square)
  then have "... = (sqrt (x^5*y*z))*(sqrt (x^5*y*z)+y^2+z^2)+y^2*(sqrt (x^5*y*z)+y^2+z^2)+z^2*(sqrt (x^5*y*z)+y^2+z^2)"
    by (simp add: semiring_normalization_rules(8))
  then have "... = ((sqrt (x^5*y*z))*sqrt (x^5*y*z)+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2)+((y^2)*(sqrt (x^5*y*z))+(y^2)*(y^2)+(y^2)*(z^2))+(z^2*(sqrt (x^5*y*z))+z^2*y^2+z^2*z^2)"
    by (simp add: distrib_left)
  then have "... = ((x^5*y*z)+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2)+((y^2)*(sqrt (x^5*y*z))+(y^2)*(y^2)+(y^2)*(z^2))+(z^2*(sqrt (x^5*y*z))+z^2*y^2+z^2*z^2)"
    using assms(1) by auto
  then have "... = ((x^5*y*z)+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2)+(sqrt (x^5*y*z)*(y^2)+(y^2)*(y^2)+(y^2)*(z^2))+((sqrt (x^5*y*z)*z^2)+z^2*y^2+z^2*z^2)"
    by simp
  then have "... = (x^5*y*z)+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2+sqrt (x^5*y*z)*(y^2)+(y^2)*(y^2)+(y^2)*(z^2)+(sqrt (x^5*y*z)*z^2)+z^2*y^2+z^2*z^2"
    by linarith
  then have "... = (x^5*y*z)+2*(sqrt (x^5*y*z))*y^2+2*(sqrt (x^5*y*z))*z^2+(y^2)*(y^2)+2*(y^2)*(z^2)+z^2*z^2"
    by force
  then have "... = (x^5*y*z)+2*(sqrt (x^5*y*z))*y^2+2*(sqrt (x^5*y*z))*z^2+(y^4)+2*(y^2)*(z^2)+z^4"
    by auto
  then show ?thesis
  by (smt \<open>(sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) = sqrt (x ^ 5 * y * z) * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) + y\<^sup>2 * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) + z\<^sup>2 * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2)\<close> \<open>(sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2)\<^sup>2 = (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2)\<close> \<open>sqrt (x ^ 5 * y * z) * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) + y\<^sup>2 * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) + z\<^sup>2 * (sqrt (x ^ 5 * y * z) + y\<^sup>2 + z\<^sup>2) = sqrt (x ^ 5 * y * z) * sqrt (x ^ 5 * y * z) + sqrt (x ^ 5 * y * z) * y\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + (y\<^sup>2 * sqrt (x ^ 5 * y * z) + y\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2) + (z\<^sup>2 * sqrt (x ^ 5 * y * z) + z\<^sup>2 * y\<^sup>2 + z\<^sup>2 * z\<^sup>2)\<close> \<open>sqrt (x ^ 5 * y * z) * sqrt (x ^ 5 * y * z) + sqrt (x ^ 5 * y * z) * y\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + (y\<^sup>2 * sqrt (x ^ 5 * y * z) + y\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2) + (z\<^sup>2 * sqrt (x ^ 5 * y * z) + z\<^sup>2 * y\<^sup>2 + z\<^sup>2 * z\<^sup>2) = x ^ 5 * y * z + sqrt (x ^ 5 * y * z) * y\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + (y\<^sup>2 * sqrt (x ^ 5 * y * z) + y\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2) + (z\<^sup>2 * sqrt (x ^ 5 * y * z) + z\<^sup>2 * y\<^sup>2 + z\<^sup>2 * z\<^sup>2)\<close> \<open>x ^ 5 * y * z + sqrt (x ^ 5 * y * z) * y\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + (y\<^sup>2 * sqrt (x ^ 5 * y * z) + y\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2) + (z\<^sup>2 * sqrt (x ^ 5 * y * z) + z\<^sup>2 * y\<^sup>2 + z\<^sup>2 * z\<^sup>2) = x ^ 5 * y * z + sqrt (x ^ 5 * y * z) * y\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + (sqrt (x ^ 5 * y * z) * y\<^sup>2 + y\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2) + (sqrt (x ^ 5 * y * z) * z\<^sup>2 + z\<^sup>2 * y\<^sup>2 + z\<^sup>2 * z\<^sup>2)\<close> \<open>x ^ 5 * y * z + sqrt (x ^ 5 * y * z) * y\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + sqrt (x ^ 5 * y * z) * y\<^sup>2 + y\<^sup>2 * y\<^sup>2 + y\<^sup>2 * z\<^sup>2 + sqrt (x ^ 5 * y * z) * z\<^sup>2 + z\<^sup>2 * y\<^sup>2 + z\<^sup>2 * z\<^sup>2 = x ^ 5 * y * z + 2 * sqrt (x ^ 5 * y * z) * y\<^sup>2 + 2 * sqrt (x ^ 5 * y * z) * z\<^sup>2 + y\<^sup>2 * y\<^sup>2 + 2 * y\<^sup>2 * z\<^sup>2 + z\<^sup>2 * z\<^sup>2\<close> semiring_normalization_rules(18))
qed
   
lemma CauchySchwarz[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1"
  shows "(x^5+y^2+z^2)*(y*z+y^2+z^2)\<ge>(sqrt (x^5*y*z)+y^2+z^2)^2"
proof-
  have 1: "(x^5+y^2+z^2)*(y*z+y^2+z^2) = x^5*(y*z+y^2+z^2) + y^2*(y*z+y^2+z^2) + z^2*(y*z+y^2+z^2)"
    by (metis (mono_tags, hide_lams) combine_common_factor linordered_field_class.sign_simps(1) ring_class.ring_distribs(2))
  then have 2: "... = (x^5)*(y*z) +(x^5)*(y^2)+(x^5)*(z^2) +(y^2)*(y*z)+(y^2)*(y^2)+(y^2)*(z^2) + (z^2)*(y*z)+(z^2)*(y^2)+(z^2)*(z^2)"
    by (simp add: distrib_left)
  then have 3: " ... = (x^5)*(y*z) +(x^5)*((y^2)+(z^2)) +(y^2)*(y*z)+(y^2)*(y^2)+(y^2)*(z^2) + (z^2)*(y*z)+(z^2)*(y^2)+(z^2)*(z^2)"
    by (simp add: linordered_field_class.sign_simps(36))
  then have 4: "... = (x^5)*(y*z) +(x^5)*((y^2)+(z^2)) +(y^2)*(y*z)+ (z^2)*(y*z)+(y^2)*(y^2)+(y^2)*(z^2) +(z^2)*(y^2)+(z^2)*(z^2)"
    by linarith
  then have 5: "... = (x^5)*(y*z) +(x^5)*((y^2)+(z^2)) +((y^2)+ (z^2))*(y*z)+(y^2)*(y^2)+(y^2)*(z^2) +(z^2)*(y^2)+(z^2)*(z^2)"
    by (smt linordered_field_class.sign_simps(20))
  then have 6: "... = (x^5)*(y*z) +(x^5)*((y^2)+(z^2)) +(y*z)*((y^2)+ (z^2))+(y^2)*(y^2)+(y^2)*(z^2) +(z^2)*(y^2)+(z^2)*(z^2)"
    by simp
  then have 7: "... = (x^5)*(y*z) +((x^5)+(y*z))*((y^2)+(z^2)) +(y^2)*(y^2)+(y^2)*(z^2) +(z^2)*(y^2)+(z^2)*(z^2)"
    by (simp add: combine_common_factor)
  then have 8: "... \<ge> (x^5)*(y*z) +(2*sqrt ((x^5)*(y*z)))*((y^2)+(z^2)) +(y^2)*(y^2)+(y^2)*(z^2) +(z^2)*(y^2)+(z^2)*(z^2)"
    using sideLemma3 
  by (smt assms(1) assms(2) power2_eq_square real_mult_le_cancel_iff1 sum_squares_le_zero_iff)
  then have 9: "... \<ge> (x^5)*(y*z)  +(2*sqrt ((x^5)*(y*z))*(y^2))+(2*sqrt ((x^5)*(y*z))*(z^2)) +(y^2)*(y^2)+(y^2)*(z^2) +(z^2)*(y^2)+(z^2)*(z^2)"
    by (simp add: linordered_field_class.sign_simps(36))
  then have 10: "... \<ge> (x^5)*(y*z)  +(2*sqrt ((x^5)*(y*z))*(y^2))+(2*sqrt ((x^5)*(y*z))*(z^2)) +(y^4)+(y^2)*(z^2) +(y^2)*(z^2)+(z^4)"
    by auto  
  then have 11: "... \<ge> (x^5)*(y*z)  +2*(sqrt ((x^5)*(y*z)))*(y^2)+2*(sqrt ((x^5)*(y*z)))*(z^2) +(y^4)+2*(y^2)*(z^2)+(z^4)"
    using combine_common_factor by linarith
  then have 12: "... \<ge>(sqrt (x^5*y*z)+y^2+z^2)^2"
    by (simp add: assms(1) assms(2))
  then show ?thesis 
  using "1" "2" "3" "4" "5" "6" "7" by presburger
qed

lemma CauchySchwarz2[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0 \<and> x*y*z\<ge>1"
  shows "(sqrt (x^5*y*z)+y^2+z^2)^2\<ge>(x^2+y^2+z^2)^2"
proof-
  have 1:"(sqrt (x^5*y*z)+y^2+z^2)^2 =(sqrt (x^5*y*z)+y^2+z^2)*(sqrt (x^5*y*z)+y^2+z^2)"
    using power2_eq_square by blast
  also have 2:"... = (sqrt (x^5*y*z))*(sqrt (x^5*y*z)+y^2+z^2)+y^2*(sqrt (x^5*y*z)+y^2+z^2)+z^2*(sqrt (x^5*y*z)+y^2+z^2)"
    by (simp add: semiring_normalization_rules(8))
  also have 3:"... = (sqrt (x^5*y*z))*(sqrt (x^5*y*z)+y^2+z^2)+((y^2)*(sqrt (x^5*y*z))+(y^2)*(y^2)+(y^2)*(z^2))+z^2*(sqrt (x^5*y*z)+y^2+z^2)"
    by (simp add: distrib_left)
  also have 4:"... = (sqrt (x^5*y*z))*(sqrt (x^5*y*z)+y^2+z^2)+((y^2)*(sqrt (x^5*y*z))+(y^2)*(y^2)+(y^2)*(z^2))+(z^2*(sqrt (x^5*y*z))+z^2*y^2+z^2*z^2)"
    by (simp add: distrib_left)
  also have 5:"... = ((sqrt (x^5*y*z))*sqrt (x^5*y*z)+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2)+((y^2)*(sqrt (x^5*y*z))+(y^2)*(y^2)+(y^2)*(z^2))+(z^2*(sqrt (x^5*y*z))+z^2*y^2+z^2*z^2)"
    by (simp add: distrib_left)
  also have 6: "... = ((sqrt (x^5*y*z))*sqrt (x^5*y*z)+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2)+((y^2)*(sqrt (x^5*y*z))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^5*y*z))+z^2*y^2+z^4)"
    using power_add by auto
  also have 7:"... = (x^5*y*z+(sqrt (x^5*y*z))*y^2+(sqrt (x^5*y*z))*z^2)+((y^2)*(sqrt (x^5*y*z))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^5*y*z))+z^2*y^2+z^4)"
    using assms by auto
  also have 8:"... = (x^4*(x*y*z)+(sqrt (x^4*(x*y*z)))*y^2+(sqrt (x^4*(x*y*z)))*z^2)+((y^2)*(sqrt (x^4*(x*y*z)))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^4*(x*y*z)))+z^2*y^2+z^4)"
    by (smt numeral_One power_add_numeral2 power_one_right semiring_norm(5) semiring_normalization_rules(18))
  also have 9:"... \<ge> (x^4*(1)+(sqrt (x^4*(x*y*z)))*y^2+(sqrt (x^4*(x*y*z)))*z^2)+((y^2)*(sqrt (x^4*(x*y*z)))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^4*(x*y*z)))+z^2*y^2+z^4)"
    using assms by auto
  then have 10:"... \<ge> (x^4*(1)+(sqrt (x^4*(1)))*y^2+(sqrt (x^4*(x*y*z)))*z^2)+((y^2)*(sqrt (x^4*(x*y*z)))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^4*(x*y*z)))+z^2*y^2+z^4)"
    by (smt assms power_not_zero real_mult_less_iff1 real_sqrt_le_mono zero_le_power)
   then have 11:"... \<ge> (x^4*(1)+(sqrt (x^4*(1)))*y^2+(sqrt (x^4*(1)))*z^2)+((y^2)*(sqrt (x^4*(x*y*z)))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^4*(x*y*z)))+z^2*y^2+z^4)"
     by (smt assms power_not_zero real_mult_less_iff1 real_sqrt_le_mono zero_le_power)
   then have 12:"... \<ge> (x^4*(1)+(sqrt (x^4*(1)))*y^2+(sqrt (x^4*(1)))*z^2)+((y^2)*(sqrt (x^4*(1)))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^4*(1)))+z^2*y^2+z^4)"
     by (smt "9" assms power_not_zero real_mult_le_cancel_iff2 real_sqrt_le_mono zero_le_power)
   then have 13:"... \<ge> (x^4+(sqrt (x^4))*y^2+(sqrt (x^4))*z^2)+((y^2)*(sqrt (x^4))+(y^4)+(y^2)*(z^2))+(z^2*(sqrt (x^4))+z^2*y^2+z^4)"
     by simp
   then have 14:"... \<ge> (x^4+(x^2)*y^2+(x^2)*z^2)+((y^2)*(x^2)+(y^4)+(y^2)*(z^2))+(z^2*(x^2)+z^2*y^2+z^4)"
     by (smt numeral_Bit0 power2_eq_square power_add real_sqrt_abs zero_le_mult_iff)
   then have 15:"... \<ge> ((x^2)*(x^2)+(x^2)*y^2+(x^2)*z^2)+((y^2)*(x^2)+(y^2)*(y^2)+(y^2)*(z^2))+(z^2*(x^2)+z^2*y^2+(z^2)*(z^2))"
     by auto
   then have 16:"...\<ge> (x^2)*(x^2+y^2+z^2) + (y^2)*((x^2)+(y^2)+(z^2))+(z^2)*((x^2)+y^2+(z^2))"
     by (simp add: ring_class.ring_distribs(1))
   then have 17:"...\<ge> (x^2+y^2+z^2)*(x^2+y^2+z^2)"
     by (smt combine_common_factor)
   then have 18:"... \<ge> (x^2+y^2+z^2)^2"
     by (simp add: power2_eq_square)
   then show ?thesis 
   using calculation by linarith 
qed

lemma sideLemma5_CauchySchwarz[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0 \<and> x*y*z\<ge>1"
  shows "(x^5+y^2+z^2)*(y*z+y^2+z^2)\<ge>(x^2+y^2+z^2)^2"
proof-
  have "(x^5+y^2+z^2)*(y*z+y^2+z^2)\<ge>(sqrt (x^5*y*z)+y^2+z^2)^2"
    using assms CauchySchwarz by blast
  then have "...\<ge>(x^2+y^2+z^2)^2"
    using assms CauchySchwarz2 by fastforce
  then show ?thesis
  by blast
qed

lemma sideLemma6[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1" 
  shows "(x^2+y^2+z^2)>0"
  by (smt assms(1) zero_less_power)

lemma sideLemma7[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1" 
  shows "y*z+y^2+z^2>0"
  by (simp add: assms(1) pos_add_strict power2_eq_square)

lemma sideLemma8[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1" 
  shows "x^5+y^2+z^2>0"
  by (smt assms(1) zero_less_power)

lemma CauchySchwarz3[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1" 
  shows "(x^2+y^2+z^2)/(x^5+y^2+z^2)\<le>(y*z+y^2+z^2)/(x^2+y^2+z^2)"
proof-
  have "(x^5+y^2+z^2)*(y*z+y^2+z^2)\<ge>(x^2+y^2+z^2)^2"
    by (simp add: assms(1) assms(2))
  then have "(x^5+y^2+z^2)*(y*z+y^2+z^2)/(x^5+y^2+z^2)\<ge>(x^2+y^2+z^2)^2/(x^5+y^2+z^2)"
  by (smt assms(1) divide_right_mono zero_less_power)
  then have "(y*z+y^2+z^2)*((x^5+y^2+z^2)/(x^5+y^2+z^2))\<ge>(x^2+y^2+z^2)^2/(x^5+y^2+z^2)"
    by auto
  then have "(y*z+y^2+z^2)\<ge>(x^2+y^2+z^2)^2/(x^5+y^2+z^2)"
    using assms(1) assms(2) sideLemma8 by fastforce
  then have "(y*z+y^2+z^2)*(1/(x^2+y^2+z^2))\<ge>((x^2+y^2+z^2)^2/(x^5+y^2+z^2))*(1/(x^2+y^2+z^2))"
    using divide_right_mono by fastforce  
  then have "(y*z+y^2+z^2)/(x^2+y^2+z^2)\<ge>(x^2+y^2+z^2)^2/((x^5+y^2+z^2)*(x^2+y^2+z^2))"
    by simp
  then have "(y*z+y^2+z^2)/(x^2+y^2+z^2)\<ge>((x^2+y^2+z^2)/(x^5+y^2+z^2))*((x^2+y^2+z^2)/(x^2+y^2+z^2))"
    by (metis (no_types, lifting) semiring_normalization_rules(29) times_divide_times_eq)
  then have "(y*z+y^2+z^2)/(x^2+y^2+z^2)\<ge>((x^2+y^2+z^2)/(x^5+y^2+z^2))"
    using sideLemma6 
    using assms(1) assms(2) by fastforce
  then show ?thesis 
  by blast
qed

lemma CauchySchwarz4_CauchySchwarz3Modified[simp]:
  fixes x y z::real
  assumes " x>0 \<and> y>0 \<and> z>0"
  assumes " x*y*z\<ge>1" 
  shows "(z^2+x^2+y^2)/(z^5+x^2+y^2)\<le>(x*y+x^2+y^2)/(z^2+x^2+y^2)"
proof-
  have "(z^5+x^2+y^2)*(x*y+x^2+y^2)\<ge>(z^2+x^2+y^2)^2"
  by (smt assms(1) assms(2) linordered_field_class.sign_simps(5) mult.assoc sideLemma5_CauchySchwarz)
  then have "(z^5+x^2+y^2)*(x*y+x^2+y^2)/(z^5+x^2+y^2)\<ge>(z^2+x^2+y^2)^2/(z^5+x^2+y^2)"
  by (smt assms(1) divide_right_mono zero_less_power)
  then have "(x*y+x^2+y^2)*((z^5+x^2+y^2)/(z^5+x^2+y^2))\<ge>(z^2+x^2+y^2)^2/(z^5+x^2+y^2)"
    by auto
  then have "(x*y+x^2+y^2)\<ge>(z^2+x^2+y^2)^2/(z^5+x^2+y^2)"
  by (smt \<open>(z\<^sup>2 + x\<^sup>2 + y\<^sup>2)\<^sup>2 / (z ^ 5 + x\<^sup>2 + y\<^sup>2) \<le> (z ^ 5 + x\<^sup>2 + y\<^sup>2) * (x * y + x\<^sup>2 + y\<^sup>2) / (z ^ 5 + x\<^sup>2 + y\<^sup>2)\<close> assms(1) nonzero_mult_div_cancel_left zero_less_power)
  then have "(x*y+x^2+y^2)*(1/(z^2+x^2+y^2))\<ge>((z^2+x^2+y^2)^2/(z^5+x^2+y^2))*(1/(z^2+x^2+y^2))"
    using divide_right_mono by fastforce  
  then have "(x*y+x^2+y^2)/(z^2+x^2+y^2)\<ge>(z^2+x^2+y^2)^2/((z^5+x^2+y^2)*(z^2+x^2+y^2))"
    by simp
  then have "(x*y+x^2+y^2)/(z^2+x^2+y^2)\<ge>((z^2+x^2+y^2)/(z^5+x^2+y^2))*((z^2+x^2+y^2)/(z^2+x^2+y^2))"
    by (metis (no_types, lifting) semiring_normalization_rules(29) times_divide_times_eq)
  then have  "(x*y+x^2+y^2)/(z^2+x^2+y^2)\<ge>((z^2+x^2+y^2)/(z^5+x^2+y^2))"
    using sideLemma6 
    using assms(1) assms(2) by fastforce
  then show ?thesis 
  by blast
qed

lemma sideLemma9[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(x^2+y^2+z^2)/(x^5+y^2+z^2)+(x^2+y^2+z^2)/(x^2+y^5+z^2)+(x^2+y^2+z^2)/(x^2+y^2+z^5) \<le> (2*(x^2+y^2+z^2) + x*y+y*z+x*z)/(x^2+y^2+z^2)"
proof-
  have 1:"(2*(x^2+y^2+z^2) + x*y+y*z+x*z)/(x^2+y^2+z^2) = ((y*z+y^2+z^2) + (x*z+x^2+z^2) + (x*y + x^2 + y^2))/(x^2+y^2+z^2)"
    by simp
  then have 2:"... = (y*z+y^2+z^2)/(x^2+y^2+z^2) + (x*z+x^2+z^2)/(x^2+y^2+z^2) +  (x*y + x^2 + y^2)/(x^2+y^2+z^2)"
    by (simp add: add_divide_distrib)
  then have 3:"... = (y*z+y^2+z^2)/(x^2+y^2+z^2) + (x*z+x^2+z^2)/(x^2+y^2+z^2) +  (x*y + x^2 + y^2)/(z^2+x^2+y^2)"
    by simp
  then have 4:"... \<ge>(y*z+y^2+z^2)/(x^2+y^2+z^2) + (x*z+x^2+z^2)/(x^2+y^2+z^2) + (z^2 + x^2 + y^2)/(z^5 + x^2 + y^2)"
    using CauchySchwarz3
    by (simp add: assms(1) assms(2))
  then have 5:"...\<ge>(y*z+y^2+z^2)/(x^2+y^2+z^2) +  (y^2 + x^2 + z^2)/(y^5 + x^2 + z^2) + (z^2 + x^2 + y^2)/(z^5 + x^2 + y^2)"
    using CauchySchwarz3
  by (smt CauchySchwarz4_CauchySchwarz3Modified assms(1) assms(2) semiring_normalization_rules(16))
  then have 6:"...\<ge>(x^2 + y^2 + z^2)/(x^5 + y^2 + z^2) +  (y^2 + x^2 + z^2)/(y^5 + x^2 + z^2) + (z^2 + x^2 + y^2)/(z^5 + x^2 + y^2)"
    using CauchySchwarz3
    by (smt assms(1) assms(2))
  then show ?thesis 
  by (smt "2")
qed

lemma sideLemma10[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(x^5-x^2)/(x^5+y^2+z^2)\<ge>1-(y*z+y^2+z^2)/(x^2+y^2+z^2)"
proof-
  have 1:"(x^5-x^2)/(x^5+y^2+z^2) = (x^5+y^2+z^2-x^2-y^2-z^2)/(x^5+y^2+z^2)"
    by simp
  then have 2:"... =((x^5+y^2+z^2)-(x^2+y^2+z^2))/(x^5+y^2+z^2)"
    by (simp add: add.commute)
  then have 3:"... = (x^5+y^2+z^2)/(x^5+y^2+z^2)-(x^2+y^2+z^2)/(x^5+y^2+z^2)"
    using diff_divide_distrib by blast
  then have 4:"... = 1 -(x^2+y^2+z^2)/(x^5+y^2+z^2)"
    by (smt assms(1) assms(2) div_self sideLemma8)
  then have 5:"...\<ge>1-(y*z+y^2+z^2)/(x^2+y^2+z^2)"
    by (simp add: assms(1) assms(2))
  then show ?thesis 
  using "3" "4" by auto
qed

lemma sideLemma11_sideLemma10Modified[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(z^5-z^2)/(z^5+x^2+y^2)\<ge>1-(x*y+x^2+y^2)/(z^2+x^2+y^2)"
proof-
  have 1:"(z^5-z^2)/(z^5+x^2+y^2) = (z^5+x^2+y^2-z^2-x^2-y^2)/(z^5+x^2+y^2)"
    by simp
  then have 2:"... =((z^5+x^2+y^2)-(z^2+x^2+y^2))/(z^5+x^2+y^2)"
    by (simp add: add.commute)
  then have 3:"... = (z^5+x^2+y^2)/(z^5+x^2+y^2)-(z^2+x^2+y^2)/(z^5+x^2+y^2)"
    using diff_divide_distrib by blast
  then have 4:"... = 1 -(z^2+x^2+y^2)/(z^5+x^2+y^2)"
    by (smt assms(1) div_self zero_less_power)
  then have 5:"...\<ge>1-(x*y+x^2+y^2)/(z^2+x^2+y^2)"
    by (simp add: assms(1) assms(2))
  then show ?thesis 
  using "3" "4" by auto
qed


lemma sideLemma12_ModifyingOriginalTheorem[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(x^5-x^2)/(x^5+y^2+z^2) + (y^5-y^2)/(y^5+x^2+z^2)+(z^5-z^2)/(z^5+x^2+y^2) \<ge>3-(2*(x^2+y^2+z^2) + x*y+y*z+x*z)/(x^2+y^2+z^2)"
proof-
  have "(x^5-x^2)/(x^5+y^2+z^2) + (y^5-y^2)/(y^5+x^2+z^2)+(z^5-z^2)/(z^5+x^2+y^2)\<ge>(x^5-x^2)/(x^5+y^2+z^2) + (y^5-y^2)/(y^5+x^2+z^2)+1-(x*y+x^2+y^2)/(z^2+x^2+y^2) "
    using sideLemma11_sideLemma10Modified
    by (simp add: assms(1) assms(2))
  then have "... \<ge>(x^5-x^2)/(x^5+y^2+z^2) + 1-(x*z+x^2+z^2)/(y^2+x^2+z^2)+1-(x*y+x^2+y^2)/(z^2+x^2+y^2) "
    using sideLemma11_sideLemma10Modified
    by (smt assms(1) assms(2) semiring_normalization_rules(16))
  then have "... \<ge>1-(y*z+y^2+z^2)/(x^2+y^2+z^2) + 1-(x*z+x^2+z^2)/(y^2+x^2+z^2)+1-(x*y+x^2+y^2)/(z^2+x^2+y^2) "
    using sideLemma10
    by (smt assms(1) assms(2))
  then have "... \<ge> 3 -(y*z+y^2+z^2)/(x^2+y^2+z^2)-(x*z+x^2+z^2)/(y^2+x^2+z^2)-(x*y+x^2+y^2)/(z^2+x^2+y^2)"
    by linarith
  then have "... \<ge> 3 -((y*z+y^2+z^2)/(x^2+y^2+z^2)+(x*z+x^2+z^2)/(y^2+x^2+z^2)+(x*y+x^2+y^2)/(z^2+x^2+y^2))"
    by linarith
  then have "...\<ge>3- ((y*z+y^2+z^2)+(x*z+x^2+z^2)+(x*y+x^2+y^2))/(z^2+x^2+y^2)"
    by (smt add_divide_distrib)
  then have "...\<ge>3- (y*z+y^2+z^2+x*z+x^2+z^2+x*y+x^2+y^2)/(z^2+x^2+y^2)"
    by smt
  then show ?thesis 
    by smt
qed

lemma sideLemma13[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "x*y+y*z+x*z \<le> x^2+y^2+z^2"
  by (smt combine_common_factor sum_squares_bound)

lemma sideLemma14[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(x*y+y*z+x*z)/(x^2+y^2+z^2) \<le> 1"
  by (simp add: assms(1) assms(2))

lemma sideLemma15[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "(2*(x^2+y^2+z^2) + x*y+y*z+x*z)/(x^2+y^2+z^2)\<ge>0"
  using assms(1) by auto

lemma FinalTheorem[simp]:
  fixes x y z::real
  assumes "x>0 \<and> y>0 \<and> z>0"
  assumes "x*y*z\<ge>1"
  shows "3\<ge>(2*(x^2+y^2+z^2) + x*y+y*z+x*z)/(x^2+y^2+z^2)"
proof-
  have 1:"(2*(x^2+y^2+z^2) + x*y+y*z+x*z)/(x^2+y^2+z^2) = (2*(x^2+y^2+z^2))/(x^2+y^2+z^2) + ( x*y+y*z+x*z)/(x^2+y^2+z^2)"
    by (simp add: divide_inverse semiring_normalization_rules(8))
  then have 2: "... =2*((x^2+y^2+z^2)/(x^2+y^2+z^2)) + ( x*y+y*z+x*z)/(x^2+y^2+z^2)"
    by linarith
  then have 3:"... = 2+( x*y+y*z+x*z)/(x^2+y^2+z^2)"
    using assms(1) assms(2) sideLemma6 by fastforce
  then have 4:"... \<le> 2+1"
    by (simp add: assms(1) assms(2))
  then show ?thesis
  using "1" "3" by linarith
qed


end
