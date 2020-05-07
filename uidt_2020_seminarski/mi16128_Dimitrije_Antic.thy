theory mi16128_Dimitrije_Antic
imports Main Complex_Main HOL.Set "HOL-Library.Infinite_Set"

begin

text\<open>
    Zadatak 2, dan 1. sa linka:
      https://imomath.com/srb/zadaci/2008_mmo.pdf

    2. (a) Dokazati da je x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 \<ge> 1
           za sve realne brojeve x, y, z takve da nijedan od njih nije jedna 1 i za
           koje vazi xyz = 1.
       (b) Dokazati da se jednakost dostize za beskonacno mnogo trojki racionalnih
           bojeva x, y, z takvih da nijedan od njih nije jedna 1 i za koje vazi xyz = 1.

    \<close>

(* a) *)
lemma nejednakost:
  assumes "(\<forall> x y z :: real. x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1)"
  shows "x^2 / (x - 1)^2 
        + y^2 / (y - 1)^2 
        + z^2 / (z - 1)^2 \<ge> 1"
  using assms by blast


type_synonym trojka_racionalnih = "rat \<times> rat \<times> rat"

(* b) Prvi nacin - koriscenjem infinite *)


fun resenje :: "trojka_racionalnih \<Rightarrow> bool" where
  "resenje (x, y, z) = (x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1  \<and>
                        x^2 / (x - 1)^2 
                        + y^2 / (y - 1)^2 
                        + z^2 / (z - 1)^2 = 1)"


lemma beskonacno_celih_resenja:
  "infinite {t :: trojka_racionalnih. resenje t} \<longleftrightarrow> True"
  sorry


(* b) Drugi nacin - definisanje prebrojivosti skupa *)

inductive konacan_skup :: "'a set \<Rightarrow> bool"
  where
    "konacan_skup {}"
  | "konacan_skup A \<Longrightarrow> konacan_skup (insert a A)"
  
abbreviation beskonacan_skup :: "'a set \<Rightarrow> bool" where
  "beskonacan_skup A == \<not> konacan_skup A"

lemma beskonacno_celih_resenja':
  "beskonacan_skup {t :: trojka_racionalnih. resenje t} \<longleftrightarrow> True"
  sorry


(* b) Treci nacin - koriscenje drugog oblika nejednakosti *)
fun resenje' :: "trojka_racionalnih \<Rightarrow> bool" where
  "resenje' (a, b, c) = (a + b + c = 1 \<and> a*b + b*c + c*a = 0)"

lemma ekvivalentno_tvrdjenje:
  fixes t :: trojka_racionalnih
  shows  "resenje t \<longleftrightarrow> resenje' t"
  sorry

value "resenje' (2/3, 2/3, -1/3)"

lemma beskonacno_celih_resenja'':
  shows "(\<forall> t :: rat. resenje' ( (t+1)/(t^2 + t + 1), (t^2 + t)/(t^2 + t + 1), (-t)/(t^2 + t + 1) )
                    \<longrightarrow> (\<exists> t1 :: rat. t1 > t \<and> resenje' ( (t1+1)/(t1^2 + t1 + 1), (t1^2 + t1)/(t1^2 + t1 + 1), (-t1)/(t1^2 + t1 + 1) ))
                     \<and> (\<exists> t2 :: rat. t2 < t \<and> resenje' ( (t2+1)/(t2^2 + t2 + 1), (t2^2 + t2)/(t2^2 + t2 + 1), (-t2)/(t2^2 + t2 + 1) )))"
  using [[show_types]]
  sorry

end

