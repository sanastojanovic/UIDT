theory mi17182_Sara_Kapetinic
  imports Complex_Main
begin

text\<open>https://www.imo-official.org/problems/IMO2016SL.pdf - teorema Algebra A1
Let a, b and c be positive real numbers such that min {ab, bc, ca} > 1. Prove that
(a^2 + 1)(b^2 + 1)(c^2 + 1) \<le> (((a + b + c)/3)^2+ 1)^3\<close>


text\<open>Pomocna leme 2 za dokaz leme ispod\<close>
lemma lema1:
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
lemma lema2 [simp]:
  fixes a d ::real
  assumes "a*d\<ge>1" "((a + d)/2)^2-1 \<ge> a*d - 1" "a*d - 1\<ge> 0"
  shows  "(a^2 + 1)*(d^2 + 1)\<le>(((a + d)/2)^2+1)^2"
proof-
  have "(a^2+1)*(d^2+1)=(a*d - 1)^2 + (a + d)^2"
    using lema1
     by simp
   also have "... \<le> (((a + d)/2)^2 - 1)^2 + (a + d)^2"
     using assms
     by simp
   also have "... = (((a + d)/2)^2)^2 - 2*((a + d)/2)^2 + 1 + (a + d)^2"
     by (simp add:Power.comm_ring_1_class.power2_diff)
   also have "... =  (((a + d)/2)^2)^2 - 2*((a + d)/2)^2 + 1 +2*(a + d)^2/2"
     by simp
   also have "... =  (((a + d)/2)^2)^2 - 2*((a + d)^2/2^2) + 2*(a + d)^2/2 + 1"
     by (smt (verit, best) power_divide)
   also have "... = (((a + d)/2)^2)^2 - 2* ((a + d)^2/4) + 4*(a + d)^2/4 +1"
     by simp
   also have "... = (((a + d)/2)^2)^2 + 2*((a + d)^2/4)+1"
     by simp
   also have "... = (((a + d)/2)^2)^2 + 2*((a + d)^2/2^2)+1"
     by simp
   also have "... = (((a + d)/2)^2)^2 + 2*((a + d)/2)^2 +1"
    by (metis power_divide)
  also have "... = (((a + d)/2)^2 + 1)^2"
    by (simp add :Power.comm_semiring_1_class.power2_sum)    
  finally show ?thesis
    by simp
qed

find_theorems "_*_ \<le> _*_"

text\<open>lema 3 ista kao prethodna ali sa drugim nazivom promenljivih zbog nekog baga koji mi nije dozvoljavao da je primenim pod drugim nazivom promenljivih\<close>
lemma lema3 [simp]:
  fixes b c ::real
  assumes "b*c\<ge>1" "((b + c)/2)^2-1 \<ge> b*c - 1" "b*c - 1\<ge> 0"
  shows  "(b^2 + 1)*(c^2 + 1)\<le>(((b + c)/2)^2+1)^2"
proof-
  have "(b^2+1)*(c^2+1)=(b*c - 1)^2 + (b + c)^2"
    using lema1
     by simp
   also have "... \<le> (((b + c)/2)^2 - 1)^2 + (b + c)^2"
     using assms
     by simp
   also have "... = (((b + c)/2)^2)^2 - 2*((b + c)/2)^2 + 1 + (b + c)^2"
     by (simp add:Power.comm_ring_1_class.power2_diff)
   also have "... =  (((b + c)/2)^2)^2 - 2*((b + c)/2)^2 + 1 +2*(b + c)^2/2"
     by simp
   also have "... =  (((b + c)/2)^2)^2 - 2*((b + c)^2/2^2) + 2*(b + c)^2/2 + 1"
     by (smt (verit, best) power_divide)
   also have "... = (((b + c)/2)^2)^2 - 2* ((b + c)^2/4) + 4*(b + c)^2/4 +1"
     by simp
   also have "... = (((b + c)/2)^2)^2 + 2*((b + c)^2/4)+1"
     by simp
   also have "... = (((b + c)/2)^2)^2 + 2*((b + c)^2/2^2)+1"
     by simp
   also have "... = (((b + c)/2)^2)^2 + 2*((b + c)/2)^2 +1"
    by (metis power_divide)
  also have "... = (((b + c)/2)^2 + 1)^2"
    by (simp add :Power.comm_semiring_1_class.power2_sum)    
  finally show ?thesis
    by simp
qed
(*
lemma lema4 :
  fixes a b c d :: real
  assumes "a*b \<ge> 1 \<and> a*c \<ge> 1 \<and> b*c \<ge> 1 \<and> a*d \<ge> 1\<and>
           a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge>0" "((b + c)/2)^2-1 \<ge> b*c - 1" "b*c - 1\<ge> 0"
        "((a + d)/2)^2-1 \<ge> a*d - 1" "a*d - 1\<ge> 0"
  shows "(a^2 + 1)*(d^2 + 1)*(b^2 + 1)*(c^2 + 1) \<le>
           (((a + d)/2)^2+1)^2 * (((b + c)/2)^2+1)^2"
proof-
  have "(a^2 + 1)*(d^2 + 1) \<le> (((a + d)/2)^2+1)^2"
    using lema2
    using assms(4) assms(5) by fastforce
  then have  "(b^2 + 1)*(c^2 + 1) \<le> (((b + c)/2)^2+1)^2"
    using lema3
    by (simp add: assms(1) assms(2))
  
  from this `(a^2 + 1)*(d^2 + 1) \<le> (((a + d)/2)^2+1)^2`
  show "(a^2 + 1)*(d^2 + 1)*(b^2 + 1)*(c^2 + 1) \<le>
           (((a + d)/2)^2+1)^2 * (((b + c)/2)^2+1)^2"
    using assms
    using Nat.mult_le_mono
    sledgehammer
qed
*)
txt\<open>Zapis glavne teoreme i pocetak dokaza\<close>
lemma
  fixes a b c d :: real
  assumes "a*b \<ge> 1 \<and> a*c \<ge> 1 \<and> b*c \<ge> 1 \<and>
           a \<ge> 0 \<and> b \<ge> 0 \<and> c \<ge>0 "
  shows "(a^2+1)*(b^2+1)*(c^2+1) \<le> (((a+b+c)/3)^2+1)^3"
  using assms
proof-
  assume "a \<ge> b \<and> b \<ge> c \<and> d = (a+b+c)/3 "
  then have "a \<ge> 1" 
    using assms
    using mult_left_le_one_le by fastforce
  then have "(a^2 + 1)*(d^2 + 1)*(b^2 + 1)*(c^2 + 1) \<le>
           (((a+d)/2)^2+1)^2 * (((b+c)/2)^2+1)^2"
    using assms    
    
qed


end