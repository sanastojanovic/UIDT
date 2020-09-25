theory mi16149_Milos_Mikovic_2

imports Complex_Main


begin

(* 
  2. Seminarski
  zadaci 5. 6. 7. sa linka : https://matematiranje.in.rs/III%20godina/6.nizovi/1.MATEMATICKA%20INDUKCIJA.pdf
  Svaki nosi po 10 poena

  
*)

(* zadatak 5 *)

lemma zadatak_5:
  fixes n :: nat
  shows "(11::nat) dvd 6^(2*n)+3^(n+2)+3^(n)"
proof(induction n)
case 0
  have "6 ^ (2 * 0) + 3 ^ (0 + 2) + 3 ^ 0 = (6::nat)^(0) + 3^(2)+(3::nat)^(0)" 
    using mult_0_right plus_nat.add_0 by presburger
  also have "... = 1 + 9 + 1" by auto
  also have "... = 11" by auto
  from this show ?case by auto
next
  case (Suc n)
  then show ?case
  proof-
  have "6 ^ (2 * Suc n) + 3 ^ (Suc n + 2) + 3 ^ Suc n = 6 ^ (2*(n+1)) + 3 ^ ((n+1)+2) + 3 ^ (n+1)" by auto
  also have "... = 6^(2*n + 2) + 3 ^ (n + 2 + 1) + 3^ (n+1)" by auto
  also have "... = (6::nat)^(2*(n::nat))*6^(2) + 3^(n+2)*3^(1) + 3 ^ (n) * 3^(1)"  by simp
  also have "... = 36*6^(2*n)+3*3^(n+2)+3*3^(n)" by auto
  also have "... = 36*6^(2*n) + (36-33)*3^(n+2) + (36-33)*3^(n)" by auto
  also have "... = 36*6^(2*n) + 36*3^(n+2)-33*3^(n+2) + 36*3^(n) - 33*3^(n)" by auto
  also have "... = 36*(6^(2*(n::nat)) + 3^(n+2) + 3^(n)) - (33::nat)*((3::nat)^(n+2) + 3^(n))" by auto
  finally show ?thesis using dvd_mult Suc by blast
qed
qed

(* Zadatak 6 *)

definition SumaN1_minus_sumaN :: "nat \<Rightarrow> real" where
  "SumaN1_minus_sumaN n = 1/(2*(2*n+1)*(n+1))"

primrec suma' :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "suma' 0 m = 0" | 
  "suma' (Suc n) m = 1 / (Suc n + m) + suma' n m"

definition suma :: "nat \<Rightarrow> real" where
  "suma n = suma' n n"

definition sumaSuc :: "nat \<Rightarrow> real" where
  "sumaSuc n = (suma n) + SumaN1_minus_sumaN n"



value "suma 3"
value "sumaSuc 2"
value "SumaN1_minus_sumaN 2"

lemma sumaSuc_vece_suma:
  fixes n :: nat
  assumes "n > 1"
  shows "suma (Suc n) \<ge> suma n"
  using assms
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case sorry
  (*
  have "suma (Suc (Suc n)) = suma' (Suc (Suc n)) (Suc (Suc n))" 
    using suma_def by blast
  also have "... = 1 / ((Suc (Suc n)) + (Suc (Suc n))) + suma' (Suc n) (Suc (Suc n))" 
    using suma'.simps(2) by blast
  also have "... =  1 / ((Suc (Suc n)) + (Suc (Suc n))) + (1 / (Suc n + (Suc (Suc n)))) + suma' n (Suc (Suc n))" 
    by simp
  *)
qed

lemma zadatak_6:
  fixes n :: nat
  assumes "n > 1"
  shows "suma n > 13/24"
  using assms
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case sorry
(*
  Ako pokazem da  suma (Suc n) \<ge> suma n onda sledi da iz IH da suma (Suc n) \<ge> 13/24 cime smo dokazali teoremu.
  Lemom sumaSuc_vece_suma pokusavam da dokazem da suma (Suc n) \<ge> suma n.
  
  have "suma (Suc n) = suma' (Suc n) (Suc n)" 
    by (simp add: suma_def) seminarski_drugi
  also have "... = 1 / (Suc n + Suc n) + suma' n (Suc n)" 
    by simp
  also have "... \<le>  1 / (Suc n + Suc n) + suma' n n"
*)
qed

  


(* Zadatak 7  *)

lemma pomocno_tvrdjenje_zadatak_7:
  fixes n :: nat
  assumes "n \<ge> 3"
  shows "2*n+1 < 2^n"
  using assms
proof (induction n)
  case 0
  then show ?case 
  by simp
next
  case (Suc n)
  show ?case
proof (cases "Suc n = 3")
  case True
  then show ?thesis by auto
next
  case False
   hence "n \<ge> 3"  
   using Suc
   by simp
  have "2 * (Suc n) + 1 = 2*(n+1) + 1" 
    by auto
  also have "... = 2*n + 3"
    by auto
  also have "... = 2*n + 1 + 2" by auto
  finally show ?thesis 
  using Suc.IH \<open>3 \<le> n\<close> by auto
qed
qed


lemma zadatak_7:
  assumes "n \<ge> 5"
  shows "2^n > n^2"
  using assms
proof (induction n)
case 0
then show ?case by auto
next
case (Suc n)
  show ?case
  proof (cases "Suc n = 5")
    case True
    then show ?thesis by auto
  next
    case False
    hence "n \<ge> 5" using Suc by auto
    have "(Suc n) ^ 2 = (n+1)*(n+1)"
      by (metis Suc_eq_plus1 power2_eq_square)
    also have "... = n^2 + 2*n + 1"
      by (simp add: power2_eq_square)
    from this have "2*n+1 < 2^n" using Suc(2) pomocno_tvrdjenje_zadatak_7[of n] by auto
    from this have "n^2 + 2*n + 1 < 2^n + 2^n" 
      using Suc.IH \<open>5 \<le> n\<close> by linarith
    finally show ?thesis 
    using \<open>(Suc n)\<^sup>2 = (n + 1) * (n + 1)\<close> \<open>(n + 1) * (n + 1) = n\<^sup>2 + 2 * n + 1\<close> \<open>n\<^sup>2 + 2 * n + 1 < 2 ^ n + 2 ^ n\<close> by auto
  qed
qed



end
