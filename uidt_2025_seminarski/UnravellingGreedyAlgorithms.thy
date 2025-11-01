theory UnravellingGreedyAlgorithms
  imports Main "HOL.HOL"
begin


(* I Specification *)

(* minBy je u knjizi nedeterministička funkcija definisana tako da vraća neku vrednost za koju važi:
     minBy f xs \<in> xs \<and> (\<forall>x \<in> xs : f (minBy f xs) \<le> f x )
   
   Dalje se koristi refinement operator (f \<leadsto> g) koji označava da za svako x, deterministicka
   funkcija g x vraća vrednost koja je moguća vrednost nedeterminističke funkcije f x.

   U Izabelu sam nedetrminističke funkcije iz knjige predstavio kao funkcije koje vraćaju skup svih
   mogućih vrednosti.
*)
definition minBy :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a set"  where
  "minBy f xs \<equiv> {x. x \<in> set xs \<and> (\<forall>y \<in> set(xs) . f x \<le> f y) }"

definition refinement :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" (infixl "\<leadsto>" 100) where
  "f \<leadsto> g \<longleftrightarrow> (\<forall>x. g x \<in> f x)"

primrec prefixes :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list list" where
  "prefixes x [] = [[[x]]]"
| "prefixes x (xs # xss) = [(x # xs) # xss] @ map ((#) xs) (prefixes x xss)"

value "prefixes (1::nat) [[3, 4],[2]]"

(* List.maps ima isto znacenje kao concatMap u haskelu *)
definition unravels :: "'a list \<Rightarrow> 'a list list list" where
  "unravels xs = foldr (List.maps \<circ> prefixes) xs [[]]"

definition all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all = list_all"

fun up :: "'a::linorder list \<Rightarrow> bool" where
  "up [] = True"
| "up [x] = True"
| "up (x # (y # xs)) = (x \<le> y \<and> up (y # xs))"

(* Ovo je takođe nedeterministička funkcija i predstavlja specifikaciju funkcije supravel *)
definition supravel_nd :: "('a::linorder list \<Rightarrow> 'a list list set)" where
  "supravel_nd \<equiv> (minBy length \<circ> filter (all up) \<circ> unravels)"


(* II Derivation *)

primrec uprefixes' :: "'a::linorder \<Rightarrow> 'a list list \<Rightarrow> 'a list list list" where
  "uprefixes' x [] = [[[x]]]"
| "uprefixes' x (xs # xss) = (if x \<le> hd xs
                               then [(x # xs) # xss] @ map ((#) xs) (uprefixes' x xss)
                               else map ((#) xs) (uprefixes' x xss))"

(* Originalna verzija funkcije uprefixes iz knjige se može videti gore kao uprefixes'. Naišao sam na
   problem da mi je bilo teško da dokažem svojstva ove funkcije jer nije striktna, tj. hd xs ne mora
   da ima rezultat. Zato sam malo izmenio funkciju tako da uvek ima rezultat. Ova funkcija će se
   ponašati isto jer nikad neće dobiti prazno xs (ali to nisam dokazao). *)
primrec uprefixes :: "'a::linorder \<Rightarrow> 'a list list \<Rightarrow> 'a list list list" where
  "uprefixes x [] = [[[x]]]"
| "uprefixes x (xs # xss) = (if xs = [] \<or> x \<le> hd xs
                               then [(x # xs) # xss] @ map ((#) xs) (uprefixes x xss)
                               else map ((#) xs) (uprefixes x xss))"

definition upravels :: "'a::linorder list \<Rightarrow> 'a list list list" where
  "upravels xs = foldr (List.maps \<circ> uprefixes) xs [[]]"


lemma foldr_fusion:
  assumes "(\<And>x y. f (g x y) = h x (f y))" and "f a = b"
  shows "(f \<circ> (\<lambda>xs. foldr g xs a)) xss = (\<lambda>xs. foldr h xs b) xss"
proof (induction xss)
  case Nil
  then show ?case using assms by auto
next
  case (Cons x xss)
  then show ?case using assms by auto
qed

(* uslov "f a = b" kako bismo mogi da primenimo foldr_fusion na unravels_upravels*)
lemma filter_all_up_empty: "filter (all up) [[]] = [[]]"
  unfolding all_def
  by auto

lemma all_up_cons: "all up (x # xs) \<longleftrightarrow> up x \<and> all up xs"
  unfolding all_def
  by auto

lemma all_up_cons2: "up (x # xs) \<and> all up (xs # xss) \<longleftrightarrow> all up ((x # xs) # xss)"
  unfolding all_def
  by (metis list_all_simps(1) neq_Nil_conv up.simps(1,3))

lemma tmp0: "\<not> all up a \<Longrightarrow> filter (all up) (prefixes x a) = []"
proof (induction a arbitrary: x)
  case Nil
  then show ?case unfolding all_def by auto
next
  case (Cons xs xss)
  then have "\<not> all up ((x # xs) # xss)" using all_up_cons2 by auto
  then have *:"filter (all up) [(x # xs) # xss] = []" by auto
  have "filter (all up) (prefixes x (xs # xss)) = filter (all up) ([(x # xs) # xss] @ map ((#) xs) (prefixes x xss))" by auto
  also have "... = filter (all up) [(x # xs) # xss] @ (filter (all up) (map ((#) xs) (prefixes x xss)))" by auto
  also from * have "... = (filter (all up) (map ((#) xs) (prefixes x xss)))" by auto
  also have "... = []"
  proof (cases "all up xss")
    case True
    then show ?thesis
      by (smt (verit, ccfv_SIG) Cons.prems Cons_eq_filterD all_def filter_map hd_map list.collapse list.simps(8) list_all_simps(1))
  next
    case False
    then show ?thesis
      by (metis (mono_tags, lifting) Cons.IH all_up_cons empty_filter_conv length_filter_map length_greater_0_conv o_apply)
  qed
  finally show ?case by auto
qed

lemma filter_all_up_map:
  assumes "up xs"
  shows "filter (all up) (map ((#) xs) xss) = map ((#) xs) (filter (all up) xss)"
  using assms all_up_cons
  by (metis (mono_tags, lifting) filter_cong filter_map o_apply)

lemma tmp1: "all up a \<Longrightarrow> filter (all up) (prefixes x a) = uprefixes x a"
proof (induction a arbitrary: x)
  case Nil
  then show ?case unfolding all_def by auto
next
  case (Cons xs xss)
  then have **: "all up xss" by (auto simp add: all_def)
  with Cons have *:"filter (all up) (prefixes x xss) = uprefixes x xss" by auto
  from Cons and ** have ***: "up xs" unfolding all_def by auto
  then show ?case
  proof (cases "xs = [] \<or> x \<le> hd xs")
    case True
    have "filter (all up) (prefixes x (xs # xss)) = filter (all up) ([(x # xs) # xss] @ map ((#) xs) (prefixes x xss))" by auto
    also have "... = filter (all up) [(x # xs) # xss] @ filter (all up) (map ((#) xs) (prefixes x xss))" by auto
    also from Cons and True have "... = [(x # xs) # xss] @ filter (all up) (map ((#) xs) (prefixes x xss))"
      unfolding all_def
      using up.elims(3) by force
    also from *** have "... = [(x # xs) # xss] @ (map ((#) xs) (filter (all up) (prefixes x xss)))" using filter_all_up_map by auto
    also from * have "... = [(x # xs) # xss] @ map ((#) xs) (uprefixes x xss)" by auto
    also from True have "... = (if xs = [] \<or> x \<le> hd xs
                               then [(x # xs) # xss] @ map ((#) xs) (uprefixes x xss)
                               else map ((#) xs) (uprefixes x xss))" by auto
    ultimately show ?thesis by auto
  next
    case f: False
    have "uprefixes x (xs # xss) = (if xs = [] \<or> x \<le> hd xs
                                    then [(x # xs) # xss] @ map ((#) xs) (uprefixes x xss)
                                    else map ((#) xs) (uprefixes x xss))" by auto
    also from f have "... = map ((#) xs) (uprefixes x xss)" by auto
    also from * have "... = map ((#) xs) (filter (all up) (prefixes x xss))" by auto
    also from *** have t:"... = filter (all up) (map ((#) xs) (prefixes x xss))" using filter_all_up_map by metis
    also from Cons have "... = filter (all up) ([(x # xs) # xss] @ (map ((#) xs) (prefixes x xss)))"
      using all_up_cons
      by (smt (verit, ccfv_threshold) append_self_conv2 calculation filter.simps(2) filter_append list.collapse t
          up.simps(3) uprefixes.simps(2))
    ultimately show ?thesis by auto
  qed
qed

(* uslov "f (g x y) = h x (f y))" kako bismo mogli da primenimo foldr_fusion na unravels_upravels*)
lemma filter_all_up_fusion: "filter (all up) ((List.maps \<circ> prefixes) x y) = (List.maps \<circ> uprefixes) x ((filter (all up)) y)"
proof (induction y arbitrary: x)
  case Nil
  then show ?case by (simp add: maps_simps(2))
next
  case (Cons xs xss)
  then show ?case
  proof (cases "all up xs")
    case True
    with Cons show ?thesis using tmp1 by (auto simp add: maps_simps)
  next
    case False
    with Cons show ?thesis using tmp0 by (auto simp add: maps_simps)
  qed
qed

lemma unravels_upravels: "filter (all up) \<circ> unravels = upravels"
  unfolding unravels_def upravels_def
  using foldr_fusion filter_all_up_empty filter_all_up_fusion
  by metis


definition heads :: "'a::linorder list list \<Rightarrow> 'a list" where
  "heads = sort \<circ> map hd"

fun order1 :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<unlhd>" 100) where
  "[] \<unlhd> _ \<longleftrightarrow> True"
| "(x # xs) \<unlhd> (y # ys) \<longleftrightarrow> x \<ge> y \<and> xs \<unlhd> ys"
| "(x # xs) \<unlhd> [] \<longleftrightarrow> False"

definition order2 :: "'a::linorder list list \<Rightarrow> 'a list list \<Rightarrow> bool" (infixl "\<preceq>" 100) where
  "ur \<preceq> vr \<longleftrightarrow> heads ur \<unlhd> heads vr"

definition minWith :: "('a::linorder list list \<Rightarrow> 'a list list \<Rightarrow> bool) \<Rightarrow> 'a list list list \<Rightarrow> 'a list list set"  where
  "minWith order urs \<equiv> {x. x \<in> set urs \<and> (\<forall>ur \<in> set urs . (order x ur))}"


lemma order1_reflexivity: "x \<unlhd> x"
proof (induction x)
  case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case by auto
qed

lemma order2_reflexivity: "x \<preceq> x"
  unfolding order2_def
  using order1_reflexivity
  by auto


lemma order1_respects_length: "x \<unlhd> y \<longrightarrow> length x \<le> length y"
proof (induction y arbitrary: x)
  case Nil
  then show ?case using order1.elims by auto
next
  case (Cons y ys)
  then show ?case
  proof (induction x)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs)
    then show ?case by auto
  qed
qed

lemma length_heads: "length (heads x) = length x"
  unfolding heads_def
  by auto

lemma minWith_minBy: "minWith (\<preceq>) x \<subseteq> minBy length x"
  unfolding order2_def minWith_def minBy_def
  using length_heads order1_respects_length
  by (smt (verit, best) Collect_mono)


(* (8.2) iz knjige *)
(* Ime insert je zauzeto pa koristimo insert' *)
lemma monotonicity_8_2: "((minWith (\<preceq>) \<circ> uprefixes x) \<leadsto> insert' x) \<longrightarrow> (ur \<preceq> vr \<longrightarrow> insert' x ur \<preceq> insert' x vr)"
  unfolding minWith_def order2_def refinement_def
  sorry

(* Redosled argumenata foldr se razlikuje u Izabelu i Haskelu pa ovo moram da zapišem drugačije nego u knjizi. *)
lemma foldr_insert: "((minWith (\<preceq>) \<circ> uprefixes x) \<leadsto> insert' x) \<longrightarrow> (\<forall>z. foldr insert' z [] \<in> (minWith (\<preceq>) \<circ> upravels) z)"
  sorry

primrec insert' :: "'a::ord \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "insert' x [] = [[x]]"
| "insert' x (xs # xss) = (if xs = [] \<or> x \<le> hd xs
                              then (x # xs) # xss
                              else xs # insert' x xss)"

lemma insert_correct: "(minWith (\<preceq>) \<circ> uprefixes x) \<leadsto> insert' x"
  unfolding refinement_def
proof (rule allI)
  fix xa
  show "insert' x xa \<in> (minWith (\<preceq>) \<circ> uprefixes x) xa"
  proof (induction xa arbitrary: x)
    case Nil
    then have "minWith (\<preceq>) [[[x]]] = {[[x]]}"
      unfolding minWith_def
      using order2_reflexivity
      by auto
    then show ?case by auto
  next
    case (Cons xs xss)
    then show ?case sorry
  qed
qed

(* Finalno rešenje *)
definition supravel :: "'a::linorder list \<Rightarrow> 'a list list" where
  "supravel x = foldr insert' x []"

value "supravel [1::nat, 3, 2]"

(* Dokaz korektnosti rešenja *)
lemma supravel_correct: "supravel_nd \<leadsto> supravel"
  unfolding supravel_def supravel_nd_def refinement_def
  using insert_correct unravels_upravels minWith_minBy foldr_insert
  by (metis comp_apply subset_iff)

end