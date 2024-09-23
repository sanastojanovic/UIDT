theory Projekat
  imports Main "HOL-Library.Char_ord"

begin

(* Funkcije za sortiranje liste listi (liste reci) *)

(* Leksikografsko poredjenje dve reci(liste) *)
fun leks :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "leks [] [] = True" |
  "leks [] _  = True" |
  "leks _ []  = False" |
  "leks (x#xs) (y#ys) = (if x < y then True else if x = y then leks xs ys else False)"

(* Ova funkcija ubacuje rec u listu sortiranih reci *)
fun ubaci :: "'a::linorder list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "ubaci x [] = [x]" |
  "ubaci x (y # ys) = (if leks x y then x # y # ys else y # ubaci x ys)"


(* Sortiramo listu listi leksikografski*)
fun sort1 :: "'a::linorder list list \<Rightarrow> 'a list list" where
  "sort1 [] = []" |
  "sort1 (x # xs) = ubaci x (sort1 xs)"


(*funkcija za racunanje pozicije polazne reci u matrici sortiranih svih rotacija reci*)
fun position1 :: "'a list \<Rightarrow> 'a list list \<Rightarrow> nat" where
  "position1 xs xss =
 length (takeWhile (\<lambda>rec_u_matrici. rec_u_matrici \<noteq> xs) xss)"

(*rotacija jedne reci*)
fun lrot :: "'a list \<Rightarrow> 'a list" where
  "lrot [] = []"
| "lrot (x#xs) = xs @ [x]"

(*ova funkacija broji koliko puta dodajemo rotiranu prethodnu rec u skup svih rotacija
reci*)
fun broj_rotacije :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "broj_rotacije xs 0 = []"
| "broj_rotacije xs (Suc n) = xs # broj_rotacije (lrot xs) n"

(*ova funkacija vraca listu svih rotacija jedne reci*)
fun rotacije :: "'a list \<Rightarrow> 'a list list" where
  "rotacije xs = broj_rotacije xs (length xs)"

(* Funkcija koja vraca poslednja slova iz matrice sortiranih rotacija *)
fun poslednja_slova :: "'a list list \<Rightarrow> 'a list" where
  "poslednja_slova [] = []"
| "poslednja_slova (x#xs) = last x # poslednja_slova xs"

(* BWT  *)
fun transform :: "'a::linorder list \<Rightarrow> ('a list * nat)" where
  "transform xs = 
     (let xss = sort1 (rotacije xs)
      in (poslednja_slova xss, position1 xs xss))"

(*Ova pomocna funkcija proverava da li je lista listi sortirana*)
fun is_sorted :: "'a::linorder list list \<Rightarrow> bool" where
  "is_sorted [] = True"
| "is_sorted [x] = True"
| "is_sorted (x#y#xs) = (leks x y \<and> (is_sorted (y#xs)))"

value "transform ''yokohama''"         
value "transform ''banana''"       
value "transform ''abc''" 



(* Dokazi *)
lemma ubaci_sortirano: "is_sorted ys \<Longrightarrow> is_sorted (ubaci x ys)"
proof (induction ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)  
  then show ?case sorry
qed


(*Dokaz korektnosti funkcije sort1 - lista je zaista sortirana*)
lemma sort1_sortirano: 
  shows "is_sorted (sort1 xs)"
  apply(induction xs)
   apply(auto simp add: ubaci_sortirano)
  done



(*Dokaz korektnosti funkcije  lrot*)
(* Rotacija jedne reci ne menja dužinu liste *)
lemma lrot_duzina: "length (lrot xs) = length xs"
  apply (induction xs)
   apply auto
  done

(* Prvo slovo reci postaje poslednje *)
lemma lrot_poslednje_slovo: "xs \<noteq> [] \<Longrightarrow> last (lrot xs) = hd xs"
  apply (induction xs)
   apply auto
  done

(* Ostatak reci se ne menja *)
lemma lrot_rest: "xs \<noteq> [] \<Longrightarrow> butlast (lrot xs) = tl xs"
  apply (induction xs)
   apply auto
  done



(*Dokaz korektnosti funkcije poslednja_slova  *)
(* Dužina krajnje reci odgovara broju redova u matrici *)
lemma poslednja_slova_length: "length (poslednja_slova xss) = length xss"
  apply (induction xss)
   apply auto
  done

lemma poslednja_slova_correct:
  assumes "\<forall>xs \<in> set xss. xs \<noteq> []"
  shows "poslednja_slova xss = map last xss"
  using assms
proof (induction xss)
  case Nil
  then show ?case by simp
next
  case (Cons a xss)
  hence IH: "poslednja_slova xss = map last xss" 
    using Cons.prems by auto
  have "poslednja_slova (a # xsss) = last a # poslednja_slova xsss" (* def *) 
    by simp
  moreover have "map last (a # xsss) = last a # map last xsss" 
    by simp
  ultimately show ?case 
    using IH by simp
qed



(*Dokaz korektnosti funkcije position*)
lemma prazna_lista: "[] ! position1 xs [] = xs \<Longrightarrow> False"
  sorry

lemma position_correct:
  assumes "xs \<in> set xss"
  shows "xss ! position1 xs xss = xs"
proof (induction xss)
  case Nil
  then show ?case
    using prazna_lista assms by auto
next
  case (Cons a xss)
  show ?case
  proof (cases "a = xs")
    case True
    then show ?thesis 
      by simp
  next
    case False
    hence "position1 xs (a # xsss) = Suc (position1 xs xsss)" 
      by simp
    moreover from Cons.IH have "xss ! position1 xs xss = xs"
      using Cons.prems False by auto
(*zelimo da pokazemo (a # xss) ! Suc (position1 xs xss) = xs i zaista je xss ! position1 xs xss = xs*)
    ultimately show ?thesis 
      by simp
  qed
qed




(*Dokaz korektnosti funkcije broj rotacije*)
lemma take_Suc_iterate_lrot:
  "take (Suc n) (iterate f xs) = xs # take n (iterate f (f xs))"
  sorry

lemma korektnost_broj_rotacije:
  "broj_rotacije xs n =  take n (iterate lrot xs)"
proof (induction n arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof -
    have "broj_rotacije xs (Suc n) = xs # broj_rotacije (lrot xs) n" (* def br_rot *)
      by simp
    also have "... = xs # take n (iterate lrot (lrot xs))"
      using Suc.IH by simp
    also have "... = take (Suc n) (iterate lrot xs)"
      by (metis take_Suc_iterate_lrot)
    finally show ?case .
  qed
qed



(*Prebacivanje funkcije ubaci u nerekurzivni oblik plus dokaz*)
fun ubaci_nonrec :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ubaci_nonrec x xs = (takeWhile (\<lambda>y. y \<le> x) xs) @ [x] @ (dropWhile (\<lambda>y. y \<le> x) xs)"


(*
lemma takeWhile_leq:
  assumes "sorted (a # xs)"
  shows "\<forall>y \<in> set (takeWhile (\<lambda>y. y \<le> x) (a # xs)). y \<le> x"
proof (cases "a \<le> x")
  case True
  then have "a \<in> set (takeWhile (\<lambda>y. y \<le> x) (a # xs))"
    by simp
  moreover have "\<forall>y \<in> set (takeWhile (\<lambda>y. y \<le> x) xs). y \<le> x"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons z zs)
    then show ?case
    proof (cases "z \<le> x")
      case True
      then have "z \<in> set (takeWhile (\<lambda>y. y \<le> x) (z # zs))"
        by simp
      moreover have "\<forall>y \<in> set (takeWhile (\<lambda>y. y \<le> x) zs). y \<le> x"
        using Cons by auto
      ultimately show ?thesis
        using True by simp
    next
      case False
      then show ?thesis
        by simp
    qed
  qed
  ultimately show ?thesis
    using True by auto
next
  case False
  then show ?thesis
    by simp
qed

lemma dropWhile_geq:
  assumes "sorted xs"
  shows "\<forall>y \<in> set (dropWhile (\<lambda>y. y \<le> x) xs). y > x"
  using assms
  apply (induction xs)
   apply auto
  done



lemma sorted_ubaci_nonrec: "sorted xs \<Longrightarrow> sorted (ubaci_nonrec x xs)"
  apply (induction xs)
   apply auto
  apply (simp add: takeWhile_leq dropWhile_geq)
  done
*)



end