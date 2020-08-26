theory mi17042_Momir_Adzemovic
  imports Main "HOL-Imperative_HOL.Array"
begin
(* Prvi deo Seminarskog *)
(* Zadatak:
  Neka je n prirodan broj. Ako su a i b prirodni brojevi vecii od 1 takvi
  da je a*b= 2*n-1, dokazati da je broj ab-(a-b)-1 oblika k*2^(2m), gde
  je k neparan prirodan, a m prirodan broj. 
*)

lemma balkanska_matematicka_olimpijada_2001_prvi_zadatak_a_ge_b:
  fixes n :: nat
  fixes a b :: int
  assumes "a > 1 \<and> b > 1 \<and> a*b = 2^n-1"
  shows "\<exists> k m ::nat . (odd k) \<and> (a*b-(a-b)-1 = k*2^m)"
  using assms
  sorry

(* Drugi Deo Seminarskog *)
definition prime :: "nat ⇒ bool"  where 
  "prime p ≡ 1 < p ∧ (∀m. m dvd p ⟶  m = 1 ∨ m = p)"

(*
  Nije moguce racunski odrediti da li je broj prost na osnovu prethodne definicije.
  Sledeca lema omogucava izracunavanje
*)
lemma prime_code[code, simp]:
  "prime p ⟷ 1 < p ∧ (∀m∈{1..p}. m dvd p ⟶  m = 1 ∨ m = p)"
  by (metis (mono_tags, hide_lams) atLeastAtMost_iff dvd_imp_le dvd_pos_nat le0 le_less_trans not_less one_dvd prime_def)

value "prime 4"
value "prime 5"

definition true_factor :: "nat ⇒ nat ⇒ bool" where
  "true_factor x y ≡ x > 1 ∧ x < y ∧ x dvd y"

(* Svaki prost broj je veci ili jednak od 2 *)
lemma prime_greater_than_2[simp]:
  "prime x ⟶ x ≥ 2"
  by (simp add: prime_def)

(* 
  Ako broj p nije prost, onda postoji z tako da vazi: 1 < z < p
  (pravi delilac) i z deli p 
*)
lemma not_prime_hence_has_true_factor:
  assumes "p > 1"
  assumes "¬ prime p"
  shows "∃z. true_factor z p"
  using assms
proof-
  from ‹¬ prime p› have "p ≤ 1 ∨ (∃m∈{1..p}. m dvd p ∧ ¬ (m = 1 ∨ m = p))"
    using assms(1) assms(2) prime_code by blast
  hence "∃m∈{1..p}. m dvd p ∧ ¬ (m = 1 ∨ m = p)"
    using ‹p > 1›
    by auto
  hence "∃m∈{1..p}. m dvd p ∧ m ≠ 1 ∧ m ≠ p"
    by auto
  hence "∃m∈{1..p}. m dvd p ∧ m > 1 ∧ m < p"
    by auto
  hence "∃m∈{1..p}. true_factor m p"
    unfolding true_factor_def
    by auto
  thus ?thesis
    by auto
qed

(* 
  Ako broj nije prost, onda ima prost delilac.
  Dokaz indukcijom, gde se pretpostavlja da vazi
  za sve brojeve manje od n
*)
lemma not_prime_hence_has_prime_true_factor:
  "∀p. (p ≥ 2 ∧ p ≤ n ∧ ¬ prime p) ⟶ (∃z. prime z ∧ true_factor z p)"
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  show ?case 
    apply (rule allI)
    apply (rule impI)
  proof-
    fix p 
    assume "2 ≤ p ∧ p ≤ Suc n ∧ ¬ prime p"
    hence "2 ≤ p" "p ≤ Suc n" "¬ prime p"
      by auto
    then show "∃z. prime z ∧ true_factor z p"
    proof-
      have "¬ prime p"
        using ‹¬ prime p› by blast
      hence "∃a. true_factor a p"
        using ‹2 ≤ p› not_prime_hence_has_true_factor by auto
      then obtain a where "true_factor a p"
        by auto
      then show ?thesis
      proof (cases "prime a")
        case True
        then show ?thesis 
          using ‹true_factor a p› by blast
      next
        case False
        hence "a ≤ n" 
          using ‹p ≤ Suc n› ‹true_factor a p› true_factor_def by auto
        hence "∃b. prime b ∧ true_factor b a"
          using False Suc.IH ‹true_factor a p› true_factor_def by auto
        then obtain b where "prime b ∧ true_factor b a"
          by auto
        hence "true_factor b p"
          using ‹true_factor a p› less_trans true_factor_def by auto
        then show ?thesis 
          using ‹prime b ∧ true_factor b a› by blast
      qed
    qed
  qed
qed

(* 
   funkcija koja 
   izbacuje sve mnozioce broja x 
   koji su veci od broja x 
   iz liste L
*)
primrec remove_multipliers :: "nat list ⇒ nat ⇒ nat list" where
  "remove_multipliers [] n = []"
| "remove_multipliers (x # xs) n = (if n dvd x ∧ x > n
                                    then remove_multipliers xs n
                                    else x # (remove_multipliers xs n))"

(* 
  Lista prirodnih brojeva do n bez jedinice.
  Lista je opadajuca, kako bi dokazi indukcijom bili jednostavniji
*)
definition nlist :: "nat ⇒ nat list" where
  "nlist n = rev [2..<n+1]"

value "remove_multipliers (nlist 100) 2"
value "remove_multipliers (nlist 1) 2"
value "remove_multipliers (nlist 2) 2"

(*
  Sledi par jednostanih i neophodnih lema za
  koje se kasnije koriste
*)
lemma nlist_suc[simp]:
  assumes "n > 0"
  shows "nlist (Suc n) = (Suc n) # (nlist n)"
  unfolding nlist_def
  using assms
  by auto

lemma nlist_suc_subset[simp]:
 "set (nlist n) ⊆ set (nlist (Suc n))"
  unfolding nlist_def
  by auto 

lemma remove_multipliers_remove_y_stays:
  assumes "y ∈ set ys"
  shows "y ∈ set (remove_multipliers ys y)"
  using assms
  by (induction ys) auto

lemma remove_multipliers_subset[simp]:
  "set (remove_multipliers xs y) ⊆ set xs"
  by (induction xs) auto

lemma remove_multipliers_nlist_subset[simp]:
  "set (remove_multipliers (nlist n) y) ⊆ set (nlist n)"
  by auto

lemma remove_multipliers_greater_y:
  assumes "y > n"
  shows "remove_multipliers (nlist n) y = nlist n"
  using assms
proof (induction n)
  case 0
  then show ?case
    unfolding nlist_def
    by auto
next
  case (Suc n)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      unfolding nlist_def
      by auto
  next
    case False
    then show ?thesis
    proof-
      have "remove_multipliers (nlist (Suc n)) y
        = remove_multipliers ((Suc n) # (nlist n)) y"
        using ‹n ≠ 0›
        by auto
      also have "...  = (Suc n) # (remove_multipliers (nlist n) y)"
        using assms(1)
        by (simp add: Suc.prems nat_dvd_not_less)
      also have "... = (Suc n) # (nlist n)"
        by (simp add: Suc.IH Suc.prems Suc_lessD)
      also have "... = nlist (Suc n)"
        using False 
        by auto
      finally show ?thesis
        by simp
    qed
  qed  
qed

lemma remove_multipliers_nlist_suc_subset[simp]:
  "set (remove_multipliers (nlist n) y) 
    ⊆ set (remove_multipliers (nlist (Suc n)) y)"
proof (cases "n > 0")
  case True
  hence *: "remove_multipliers (nlist (Suc n)) y
        = remove_multipliers ((Suc n) # (nlist n)) y"
    by simp 

  case True
  then show ?thesis
  proof (cases "(Suc n) ≤ y")
    case True
    hence **: ‹¬(y dvd (Suc n) ∧ (Suc n) > y)›
      by auto
    case True
    then show ?thesis
    proof-
      from * have "remove_multipliers (nlist (Suc n)) y 
            = remove_multipliers ((Suc n) # (nlist n)) y"
        by simp
      also have "... = (Suc n) # remove_multipliers (nlist n) y"
        using ‹¬(y dvd (Suc n) ∧ (Suc n) > y)›
        by auto
      also have "set ((Suc n) # remove_multipliers (nlist n) y)
            = {Suc n} ∪ set (remove_multipliers (nlist n) y)"
        by auto
      finally have "set (remove_multipliers (nlist n) y)
                     ⊆ set (remove_multipliers (nlist (Suc n)) y)"
        by auto
      thus ?thesis
        by simp
    qed
  next
    case False
    then show ?thesis
    proof (cases "y dvd (Suc n)")
      case True
      hence ***: ‹y dvd (Suc n) ∧ (Suc n) > y›
        using ‹¬ (Suc n ≤ y)›
        by auto
        case True
      then show ?thesis
      proof-
        from * have "remove_multipliers (nlist (Suc n)) y 
              = remove_multipliers ((Suc n) # (nlist n)) y"
          by simp
        also have "... = remove_multipliers (nlist n) y"
          using ‹y dvd (Suc n) ∧ (Suc n) > y›
          by simp
        finally have "set (remove_multipliers (nlist n) y)
                     ⊆ set (remove_multipliers (nlist (Suc n)) y)"
        by simp
      thus  ?thesis
          by simp
      qed
    next
      case False
      hence **: ‹¬(y dvd (Suc n) ∧ (Suc n) > y)›
        by auto
      case False
      then show ?thesis
      proof-
      from * have "remove_multipliers (nlist (Suc n)) y 
            = remove_multipliers ((Suc n) # (nlist n)) y"
        by simp
      also have "... = (Suc n) # remove_multipliers (nlist n) y"
        using ‹¬(y dvd (Suc n) ∧ (Suc n) > y)›
        by auto
      also have "set ((Suc n) # remove_multipliers (nlist n) y)
            = {Suc n} ∪ set (remove_multipliers (nlist n) y)"
        by auto
      finally have "set (remove_multipliers (nlist n) y)
                     ⊆ set (remove_multipliers (nlist (Suc n)) y)"
        by auto
      thus ?thesis
        by simp
      qed
    qed
  qed
next
  case False 
  then show ?thesis
    unfolding nlist_def
    by auto
qed

lemma remove_multipliers_suc_subset[simp]:
  "set (remove_multipliers (nlist (Suc n)) y)
   ⊆ {Suc n} ∪ (set (remove_multipliers (nlist n) y))"
  unfolding nlist_def
  by auto

(*
  Izbacivanje svih mnozioca broja y je ekvivaletno izbacivanju
  svakog broja x > y za koji vazi da y deli x
*)
theorem remove_multipliers_theorem1:
  fixes x y n :: nat
  assumes "y ≥ 2"
  assumes "x ≤ n ∧ x > y"
  shows "x ∈ set (remove_multipliers (nlist n) y) ⟷ ¬ (y dvd x)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n) 
  then show ?case 
  proof (cases "x = Suc n")
    case True
    then show ?thesis
    proof (cases "y dvd Suc n")
      case True
      then show ?thesis 
      proof-
        have "remove_multipliers (nlist (Suc n)) y
          = remove_multipliers ((Suc n) # (nlist n)) y"
          by (metis One_nat_def True assms(1) dvd_imp_le neq0_conv nlist_suc not_less_eq_eq one_add_one plus_1_eq_Suc zero_less_Suc)
        hence "... = remove_multipliers (nlist n) y"
          using Suc.prems(2) True by auto
        have "(Suc n) ∉ set (remove_multipliers (nlist n) y)"
          by (metis Groups.add_ac(2) Suc_n_not_le_n atLeastAtMost_iff atLeastLessThanSuc_atLeastAtMost in_mono nlist_def one_add_one plus_1_eq_Suc remove_multipliers_subset set_rev set_upt)
        hence "x ∉ set (remove_multipliers (nlist n) y)"
          using ‹x = Suc n›
          by blast
        hence "x ∉ set (remove_multipliers (nlist (Suc n)) y)"
          using ‹remove_multipliers (Suc n # nlist n) y = remove_multipliers (nlist n) y› ‹remove_multipliers (nlist (Suc n)) y = remove_multipliers (Suc n # nlist n) y› 
          by auto
        show ?thesis
          using Suc.IH Suc.prems(2) True ‹x ∉ set (remove_multipliers (nlist (Suc n)) y)› ‹x ∉ set (remove_multipliers (nlist n) y)› assms(1) le_Suc_eq by blast
    qed
    next
      case False
      then show ?thesis 
      proof-
        have "remove_multipliers (nlist (Suc n)) y
          = remove_multipliers ((Suc n) # (nlist n)) y"
          using Suc.prems(2) assms(1) by auto
        hence "... = (Suc n) # remove_multipliers (nlist n) y"
          by (simp add: False)
        have "(Suc n) ∈ set ((Suc n) # remove_multipliers (nlist n) y)"
          by simp
        hence "x ∈ set ((Suc n) # remove_multipliers (nlist n) y)"
          using True 
          by blast
        hence "x ∈ set (remove_multipliers (nlist (Suc n)) y)"
          using ‹remove_multipliers (Suc n # nlist n) y = Suc n # remove_multipliers (nlist n) y› ‹remove_multipliers (nlist (Suc n)) y = remove_multipliers (Suc n # nlist n) y› 
          by auto
        thus ?thesis
          using False True by blast
      qed
    qed
  next
    case False
    hence *: "x ∈ set (remove_multipliers (nlist n) y) ⟷ ¬ (y dvd x)"
      using Suc.IH Suc.prems(2) assms(1) le_SucE by blast
    have "set (remove_multipliers (nlist (Suc n)) y)
        ⊆ {Suc n} ∪ (set (remove_multipliers (nlist n) y))"
      using remove_multipliers_suc_subset by simp
    hence "x ∈ set (remove_multipliers (nlist (Suc n)) y)
        ⟶ x = (Suc n) ∨ x ∈ set (remove_multipliers (nlist n) y)"
      by auto
    from this and ‹x ≠ Suc n› have **: 
       "x ∈ set (remove_multipliers (nlist (Suc n)) y)
        ⟶ x ∈ set (remove_multipliers (nlist n) y)"
      by auto
    case False
    then show ?thesis
      using ‹x ≠ Suc n›
      using * and **
      using remove_multipliers_nlist_suc_subset 
      by blast
  qed
qed

(*
  Direktna posledica prethodne teoreme:
  f-ja "remove_multipliers" ne brise proste brojeve
*)
theorem remove_multipliers_theorem1_cons:
  fixes x y n :: nat
  assumes "prime x"
  assumes "y ≥ 2"
  assumes "x ≤ n ∧ x > y"
  shows "x ∈ set (remove_multipliers (nlist n) y)"
  using assms
  using prime_def remove_multipliers_theorem1 by auto

(*
  Jaca verzija prethodne teoreme
*)
theorem remove_multipliers_theorem2:
  assumes "prime x"
  assumes "x ∈ set xs"
  assumes "x ≠ y"
  assumes "y ≥ 2"
  shows "x ∈ set (remove_multipliers xs y)"
  using assms
proof (induction xs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases "a > y")
    case True
    then show ?thesis
    proof (cases "y dvd a")
      case True
      then show ?thesis
      proof-
        from ‹a > y› and ‹y dvd a› have "y dvd a ∧ a > y"
          by simp
        hence "remove_multipliers (a # xs) y = remove_multipliers xs y"
          by auto
        also have ‹x ∈ set (remove_multipliers xs y)› 
          by (metis Cons.IH Cons.prems(2) True ‹y < a› ‹y dvd a ∧ y < a› assms(1) assms(3) assms(4) less_imp_triv not_less remove_multipliers_theorem1 remove_multipliers_theorem1_cons set_ConsD)
        finally show ?thesis
          by simp
      qed
    next
      case False
      then show ?thesis 
        using Cons.IH Cons.prems(2) assms(1) assms(3) assms(4) by auto
    qed
  next
    case False
    then show ?thesis 
      using Cons.IH Cons.prems(2) assms(1) assms(3) assms(4) by auto
  qed
qed

(*
  Ako u listi xs postoji broj y koji je pravi delilac broja z,
  onda broj nakon uklanjanja svih mnozioca broja y, 
  u listi xs se ne nalazi broj z
*)
lemma remove_multipliers_true_factor:
  assumes "true_factor z y"
  shows "y ∉ set (remove_multipliers xs z)"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases "a = y")
    case True
    then show ?thesis
      using Cons.IH assms true_factor_def by auto
  next
    case False
    then show ?thesis 
      using Cons.IH assms by auto
  qed
qed

(* Erastostenovo Sito *)
(*
  erast' je pomocna f-ja preko
  koje se definise f-ja za Erastostenovo sito
*)
primrec erast' :: "nat list ⇒ nat list ⇒ nat list" where
  "erast' [] ys = ys"
| "erast' (x # xs) ys = (let es = erast' xs ys
                         in (if x ∈ set es
                             then remove_multipliers es x
                             else es))"
(*
  Posto je (nlist n) opadajuca f-ja,
  rezultat se rotira kako bi bio rastuci
*)
definition erast :: "nat ⇒ nat list" where
  "erast n = rev (erast' (nlist n) (nlist n))"

value "erast 100"

lemma erast_0:
  "erast 0 = []"
  unfolding erast_def nlist_def
  by auto

(*
  Vazi sledece:
  set (erast' [a1, a2, ..., an] bs)
  ⊆ set (erast' [a2, ..., an] bs)
  ...
  ⊆ set (erast' [an] bs)
  ⊆ set (erast' [] bs)
  = bs
*)
lemma erast'_next_sub:
  "set (erast' (x # xs) ys) ⊆ set (erast' xs ys)"
proof (cases "x ∈ set (erast' xs ys)")
  case True
  then show ?thesis
  proof-
    have "erast' (x # xs) ys = remove_multipliers (erast' xs ys) x"
      using True
      by auto
    hence "set (erast' (x # xs) ys) ⊆ set (remove_multipliers (erast' xs ys) x)"
      by auto
    thus "set (erast' (x # xs) ys) ⊆ set (erast' xs ys)"
      using remove_multipliers_subset
      by blast
  qed
next
  case False
  then show ?thesis
    by auto
qed

(*
  Direktna posledica prethodne leme
*)
lemma erast'_nlist_sub:
  "set (erast' xs ys) ⊆ set ys"
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  then show ?case
    by (meson dual_order.trans erast'_next_sub)
qed

(*
  Specijalan slucaj prethodne leme koji se cesce koristi
*)
lemma erast_nlist_sub:
  "set (erast n) ⊆ set (nlist n)"
  unfolding erast_def
  by (simp add: erast'_nlist_sub)

(*
  F-ja erast (tj. erast') ne brise proste brojeve iz list
  tj. oni uvek opstaju

  Ovo predstavlja jednu od kljucnih lema u dokazu korektnosti
  Erastostenovog sita
*)
lemma erast'_prime_stays:
  assumes "prime y"
  assumes "y ∈ set ys"
  shows "y ∈ set (erast' (nlist n) ys)"
proof (induction n)
  case 0
  then show ?case
    unfolding nlist_def
    by (simp add: assms(2))
next
  case (Suc n)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      unfolding nlist_def
      by (simp add: assms(2))
  next
    case False
    hence *: "erast' (nlist (Suc n)) ys = erast' ((Suc n) # (nlist n)) ys"
      by simp
    case False
    then show ?thesis 
    proof (cases "(Suc n) ∈ set (erast' (nlist n) ys)")
      case True
      from this and * have **: "erast' (nlist (Suc n)) ys = 
        remove_multipliers (erast' (nlist n) ys) (Suc n)"
        by simp
      case True
      then show ?thesis
      proof (cases "y = Suc n")
        case True
        then show ?thesis
        proof-
          from ‹y = Suc n› and ‹y ∈ set (erast' (nlist n) ys)› have 
            "y ∈ set (remove_multipliers (erast' (nlist n) ys) (Suc n))"
            using remove_multipliers_remove_y_stays 
            by simp
          from this and ** show ?thesis
            by simp
        qed
      next
        case False
        then show ?thesis
          using "**" Suc.IH assms(1) nlist_def remove_multipliers_theorem2 by fastforce
      qed
    next
      case False
      hence "erast' (nlist (Suc n)) ys = erast' (nlist n) ys"
        by (simp add: "*")
      case False
      then show ?thesis 
        by (simp add: Suc.IH ‹erast' (nlist (Suc n)) ys = erast' (nlist n) ys›)
    qed
  qed
qed

(*
  Posledica prethodne leme
  Predstavlja jedan kljucni smer u dokazu korektnosti Erastostenovog sita
*)
theorem erast_prime_stays:
  assumes "prime y"
  assumes "y ≤ n"
  shows "y ∈ set (erast n)" 
  using assms
proof (induction n)
case 0
  then show ?case 
    using prime_def by blast
next
  case (Suc n)
  then show ?case
  proof-
    have "y ∈ set (nlist (Suc n))"
      by (metis (full_types) One_nat_def Suc.IH Suc.prems(2) assms(1) erast_nlist_sub le_SucE list.set_intros(1) nat_less_le nlist_suc nlist_suc_subset prime_def subset_eq zero_less_Suc)
    hence "y ∈ set (erast' (nlist (Suc n)) (nlist (Suc n)))"
      using assms(1) erast'_prime_stays by blast
    thus "y ∈ set (erast (Suc n))"
      by (simp add: erast_def)
  qed
qed

lemma erast'_less_than_n:
  assumes "y ∈ set (erast' (nlist n) (nlist n))"
  shows "y ≤ n"
  using assms erast'_nlist_sub nlist_def by fastforce

(*
  Svi brojevi u Erastostenovom situ su
  izmedju 2 i n, gde je n zadati parametar f-je
*)
lemma erast_y_less_than_n:
  assumes "y ∈ set (erast' (nlist n) (nlist n))"
  shows "y > 1 ∧ y ≤ n"
proof-
  from assms have "y ∈ set (nlist n)"
    using erast'_nlist_sub by blast
  thus "y > 1 ∧ y ≤ n"
    using nlist_def
    by auto
qed

(*
  Direktna posledica lema: erast'_next_sub
*)
lemma erast'_less_removals_sub:
  shows "set (erast' (cs @ as) ys) ⊆ set (erast' as ys)"
proof (induction cs)
  case Nil
  then show ?case
    by simp
next
  case (Cons c cs)
  then show ?case 
  proof (cases "c ∈ set(erast' (cs @ as) ys)")
    case True
    then show ?thesis
      by (metis Cons.IH append_Cons dual_order.trans erast'_next_sub)
  next
    case False
    then show ?thesis 
      using Cons.IH by auto
  qed

qed

(*
  Ako broj ima prost delilac, onda on ce on
  biti izbrisan u Erastostenovom situ 
*)
lemma erast_prime_true_factor_deletes:
  assumes "prime z"
  assumes "true_factor z y"
  assumes "y ≤ n"
  shows "y ∉ set (erast n)"
  using assms
proof-
  have "z ∈ set (nlist n)"
    by (meson assms(1) assms(2) assms(3) erast_nlist_sub erast_prime_stays less_imp_le_nat less_le_trans subset_iff true_factor_def)
  hence "z ∈ set (erast n)"
    using assms(1) assms(2) assms(3) erast_prime_stays true_factor_def by auto
  from ‹z ∈ set (nlist n)› have "∃as bs. (nlist n) = as @ [z] @ bs"
    by (simp add: split_list)
  then obtain as bs where "(nlist n) = as @ [z] @ bs"
    by auto
  hence "set ([z] @ bs) ⊆ set (as @ [z] @ bs)"
    by (simp add: subset_iff)
  have "set (erast' (nlist n) (nlist n)) = set(erast' (as @ [z] @ bs) (nlist n))"
    using ‹nlist n = as @ [z] @ bs› by auto
  hence "... ⊆ set(erast' ([z] @ bs) (nlist n))"
    using erast'_less_removals_sub by blast
  have "z ∈ set(erast' bs (nlist n))"
    by (metis Cons_eq_appendI ‹nlist n = as @ [z] @ bs› ‹set (erast' (as @ [z] @ bs) (nlist n)) ⊆ set (erast' ([z] @ bs) (nlist n))› ‹z ∈ set (nlist n)› append_self_conv2 assms(1) erast'_next_sub erast'_prime_stays in_mono)
  hence "erast' ([z] @ bs) (nlist n)
     = remove_multipliers (erast' bs (nlist n)) z"
    by auto
  hence "y ∉ set (remove_multipliers (erast' bs (nlist n)) z)"
    using assms(2) remove_multipliers_true_factor by blast
  hence "y ∉ set (erast' ([z] @ bs) (nlist n))"
    using ‹erast' ([z] @ bs) (nlist n) = remove_multipliers (erast' bs (nlist n)) z› by auto
  thus "y ∉ set (erast n)"
    using ‹nlist n = as @ [z] @ bs› ‹set (erast' (as @ [z] @ bs) (nlist n)) ⊆ set (erast' ([z] @ bs) (nlist n))› erast_def by auto
qed

(*
  Opstiji slucaj prethodne leme (z ne mora da bude prost broj)
*)
lemma erast_true_factor_deletes:
  assumes "true_factor z y"
  assumes "y ≤ n"
  shows "y ∉ set (erast n)"
  using assms
proof (cases "prime z")
  case True
  then show ?thesis 
    using assms(1) assms(2) erast_prime_true_factor_deletes by blast
next
  case False
  hence "∃s. true_factor s z ∧ prime s"
    by (metis (full_types) One_nat_def Suc_1 Suc_leI assms(1) le_refl not_prime_hence_has_prime_true_factor true_factor_def)
 then obtain s where "true_factor s z ∧ prime s"
    by auto
  hence "true_factor s y"
    using assms(1) less_trans true_factor_def by auto
  then show ?thesis
    using ‹true_factor s z ∧ prime s› assms(2) erast_prime_true_factor_deletes by blast
qed

(*
  Prosti brojevi ostaju u Erastostenovom situ
*)
lemma erast'_keeps_prime:
  assumes "y ≤ n"
  assumes "y ∈ set (erast' (nlist n) (nlist n))"
  shows "prime y"
  apply (rule ccontr)
proof-
  assume "¬ prime y"
  then show False
  proof-
    from ‹¬ prime y› have "∃z. true_factor z y"
      unfolding true_factor_def
      by (metis assms(2) atLeastAtMost_iff erast_y_less_than_n le_neq_implies_less prime_code)
    then obtain z where "true_factor z y"
      by auto
    hence "z ∈ set (nlist n)"
      unfolding true_factor_def
      using assms(1) nlist_def by auto
    hence "y ∉ set (erast' (nlist n) (nlist n))"
      using true_factor_def
      using ‹true_factor z y› assms(1) erast_def erast_true_factor_deletes by auto
    from this and assms show "False"
      by auto
  qed
qed

(*
  Ekvivaletno prethodnoj lemi (posledica)
  Predstavlja drugi kljucni smer u dokazivanju korektnosti
  Erastostenovog sita
*)
theorem erast_keeps_prime:
  assumes "y ∈ set (erast n)"
  shows "prime y"
  using assms erast'_keeps_prime erast_def erast_y_less_than_n by auto

(*
  Broj x se nalazi u Erastostenovom situ
    akko
  broj x je prost broj
*)
theorem erast_prime:
  fixes x n :: nat
  assumes "x ≤ n"
  shows "x ∈ set (erast n) ⟷ prime x"
  using assms
  using erast_keeps_prime erast_prime_stays by blast

end