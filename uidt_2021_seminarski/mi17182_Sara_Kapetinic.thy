theory mi17182_Sara_Kapetinic
  imports Complex_Main
begin

text\<open>Pomocna lema za dokaz leme ispod\<close>
lemma helpLemma:
  fixes a b ::real
  shows "(a^2+1)*(b^2+1) = (a*b - 1)^2 + (a + b)^2"
proof-
  have "(a*b - 1)^2 + (a + b)^2 = (a*b -1)^2 + a^2+2*a*b + b^2"
    by (simp add :power2_sum)
  also have "... = (a*b)^2 - 2*a*b + 1 + a^2 + 2*a*b + b^2"
    by (simp add:Power.comm_ring_1_class.power2_diff)
  also have "... = a^2*b^2 + a^2 + b^2 + 1" 
    by (simp add: power_mult_distrib)
  also have "... = a^2*(b^2 + 1) + b^2 + 1" 
    by (simp add: distrib_left)
  finally show ?thesis 
    by (simp add: distrib_right)
qed

text\<open>Pomocna lema za dokazivanje glavne teoreme\<close>
lemma helpLemmaForMainTheorem:
  fixes a b ::real
  assumes "a*b\<ge>1" "((a+b)/2)^2-1 \<ge> a*b-1" "a*b-1\<ge> 0"
  shows  "(a^2+1)*(b^2+1)\<le>(((a+b)/2)^2+1)^2"
proof-
  have "(a^2+1)*(b^2+1)=(a*b - 1)^2 + (a + b)^2"
    using helpLemma
     by simp
   also have "... \<le> (((a + b)/2)^2 - 1)^2 + (a + b)^2"
     using assms
     by simp
   also have "... = (((a+b)/2)^2)^2 - 2*((a+b)/2)^2 + 1 + (a + b)^2"
     by (simp add:Power.comm_ring_1_class.power2_diff)
   also have "... =  (((a+b)/2)^2)^2 - 2*((a + b)/2)^2 + 1 +2*(a + b)^2/2"
     by simp
   also have "... =  (((a+b)/2)^2)^2 - 2*((a+b)^2/2^2) + 2*(a+b)^2/2 + 1"
     by (smt (verit, best) power_divide)
   also have "... = (((a+b)/2)^2)^2 - 2* ((a+b)^2/4) + 4*(a+b)^2/4 +1"
     by simp
   also have "... = (((a+b)/2)^2)^2 + 2*((a+b)^2/4)+1"
     by simp
   also have "... = (((a+b)/2)^2)^2 + 2*((a+b)^2/2^2)+1"
     by simp
   also have "... = (((a+b)/2)^2)^2 + 2*((a + b)/2)^2 +1"
    by (metis power_divide)
  also have "... = (((a+b)/2)^2+1)^2"
    by (simp add :Power.comm_semiring_1_class.power2_sum)    
  finally show ?thesis
    by simp
qed

txt\<open>Zapis glavne teoreme\<close>
lemma
  fixes a b c :: real
  assumes "a*b \<le> 1 \<and> a*c \<le> 1 \<and> b*c \<le> 1 \<and>
           a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge>0"
  shows "(a^2+1)*(b^2+1)*(c^2+1) \<le> (((a+b+c)/3)^2+1)^3"
  sorry


end