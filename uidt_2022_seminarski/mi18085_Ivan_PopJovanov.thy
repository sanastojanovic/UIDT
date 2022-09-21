theory mi18085_Ivan_PopJovanov
  imports Main "HOL-Hoare.Hoare_Logic"
begin

text \<open>
Семинарски

Дат је скуп природних бројева (задат у облику сортираног низа). Одредити најмањи природан број који није
збир неких елемената тог скупа (сваки елемент скупа може само једном учествовати у збиру).

Стране 14-15: 
http://poincare.matf.bg.ac.rs/~filip/asp/01_asp_korektnost.pdf

Две рекурзивне имплементације и итеративна имплементација преко Хорове логике.

Није довршено.
\<close>

definition test_xs_1 :: "nat list" where
  "test_xs_1 = [1, 2, 4, 7, 15, 32, 35, 48]"

definition test_xs_2 :: "nat list" where
  "test_xs_2 = [1, 2, 3, 5, 14, 20, 27]"

fun algoritam_rekurzivno' :: "nat list \<Rightarrow> nat => nat" where
  "algoritam_rekurzivno' [] mozeDo = mozeDo + 1" |
  "algoritam_rekurzivno' (x#xs) mozeDo = (
    if x > mozeDo + 1 then mozeDo + 1
    else algoritam_rekurzivno' xs (mozeDo + x)
  )"

fun algoritam_rekurzivno :: "nat list \<Rightarrow> nat" where
  "algoritam_rekurzivno xs = algoritam_rekurzivno' xs 0"

fun algoritam_rekurzivno_u_nazad' :: "nat list \<Rightarrow> nat" where
  "algoritam_rekurzivno_u_nazad' [] = 1" |
  "algoritam_rekurzivno_u_nazad' (x#xs) = (
    let m = algoritam_rekurzivno_u_nazad' xs in
    if x > m then m
    else m + x
  )"

fun algoritam_rekurzivno_u_nazad :: "nat list \<Rightarrow> nat" where
  "algoritam_rekurzivno_u_nazad xs = algoritam_rekurzivno_u_nazad' (rev xs)"

value "test_xs_1"
value "algoritam_rekurzivno test_xs_1"
value "algoritam_rekurzivno_u_nazad test_xs_1"

value "test_xs_2"
value "algoritam_rekurzivno test_xs_2"
value "algoritam_rekurzivno_u_nazad test_xs_2"

definition moze :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "moze x xs \<longleftrightarrow> (\<exists>a \<subseteq> (set xs). x = sum id a)"

lemma [simp]:
  "algoritam_rekurzivno_u_nazad' xs \<le> (sum_list xs) + 1"
  apply (induction xs)
   apply auto
  apply (smt (verit, best) add.commute add_diff_cancel_left' diff_Suc_diff_eq1 diff_is_0_eq le_SucI le_add1 less_imp_le_nat trans_le_add2)
  done

lemma [simp]:
  "algoritam_rekurzivno_u_nazad' (x#xs) = (sum_list (x#xs)) + 1 \<longrightarrow> algoritam_rekurzivno_u_nazad' (xs) = (sum_list (xs)) + 1"
  apply (induction xs)
   apply simp
  apply (smt (verit, ccfv_threshold) add.commute add_Suc_right add_right_cancel algoritam_rekurzivno_u_nazad'.simps(2) not_add_less1 plus_1_eq_Suc sum_list.Cons)
  done

lemma [simp]:
  assumes "sorted (rev (x#xs))" "distinct (x#xs)"
  assumes "(\<forall>x\<in>(set (x#xs)). x > 0)"
  shows "algoritam_rekurzivno_u_nazad' (x#xs) < (sum_list (x#xs)) + 1 \<longrightarrow> algoritam_rekurzivno_u_nazad' (x#xs) = algoritam_rekurzivno_u_nazad' (xs)"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  hence "a < x"
    using \<open>sorted (rev (x # a # xs))\<close> \<open>distinct (x#a#xs)\<close>
    by (metis distinct_length_2_or_more list.set_intros(1) order.strict_iff_order rev.simps(2) set_rev sorted_append)
  thus ?case 
    using Cons
    sorry
qed
  
theorem Korektnost:
  assumes "sorted xs" "distinct xs"
  assumes "(\<forall>x\<in>(set xs). x > 0)"
  assumes "r = algoritam_rekurzivno_u_nazad xs"
  shows "(\<forall>a \<subseteq> (set xs). r \<noteq> sum id a)"
  using assms
  unfolding moze_def
proof (induction xs arbitrary: r)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    sorry
qed

lemma
  "algoritam_rekurzivno_u_nazad xs = algoritam_rekurzivno xs"
  apply (induction xs)
   apply simp
  sorry

text \<open>Итеративно решење преко Хорове логике.\<close>

lemma [simp]:
  assumes "length xs > i"
  shows "sum_list (take i xs) + xs ! i = sum_list (take (Suc i) xs)"
  using assms
  by (simp add: take_Suc_conv_app_nth)

text \<open>Заустављање\<close>

lemma zaustavljanje: "VARS mozeDo i (xs::nat list) x (nadjen::bool) rezultat
  [sorted xs \<and> distinct xs \<and> xs = (X::nat list)]
  rezultat := (sum_list xs) + 1;
  nadjen := False;
  mozeDo := 0;
  i := (0::nat);
  WHILE i < length xs \<and> \<not>nadjen
  INV {0 \<le> i \<and> i \<le> length xs \<and> mozeDo = sum_list (take i xs)}
  VAR {(length xs)-i}
  DO 
  x := xs!i;
  IF x > mozeDo + 1 \<and> \<not>nadjen
  THEN 
  nadjen := True;
  rezultat := mozeDo + 1
  ELSE SKIP FI;
  mozeDo := mozeDo + x;
  i := i+1
  OD
  [i = length xs \<or> nadjen]"
  apply vcg_tc_simp
    apply auto
  done

definition moze_se_dobiti :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "moze_se_dobiti m xs \<longleftrightarrow> (\<exists>a\<subseteq>(set xs). m = sum id a)"

text \<open>Инваријанта петље\<close>

lemma invarijanta_petlje: "VARS (mozeDo::nat) i (xs::nat list) x (nadjen::bool) rezultat
  [sorted xs \<and> distinct xs \<and> xs = (X::nat list)]
  rezultat := (sum_list xs) + 1;
  nadjen := False;
  mozeDo := 0;
  i := (0::nat);
  WHILE i < length xs \<and> \<not>nadjen
  INV {0 \<le> i \<and> i \<le> length xs \<and> mozeDo = sum_list (take i xs) \<and> (\<forall>br\<in>{0..<mozeDo+1}. moze_se_dobiti br (take i xs))}
  VAR {(length xs)-i}
  DO 
  x := xs!i;
  IF x > mozeDo + 1 \<and> \<not>nadjen
  THEN 
  nadjen := True;
  rezultat := mozeDo + 1
  ELSE SKIP FI;
  mozeDo := mozeDo + x;
  i := i+1
  OD
  [i = length xs \<or> nadjen]"
  unfolding moze_se_dobiti_def
  apply vcg_tc_simp
proof 
  show "\<And>i xs nadjen.
       i \<le> length xs \<and> (\<forall>br\<in>{0..<Suc (sum_list (take i xs))}. \<exists>a\<subseteq>set (take i xs). br = \<Sum> a) \<and> i < length xs \<and> \<not> nadjen \<Longrightarrow>
       \<forall>br\<in>{0..<Suc (sum_list (take (Suc i) xs))}. \<exists>a\<subseteq>set (take (Suc i) xs). br = \<Sum> a" 
    apply (erule conjE) +
    apply simp
  proof 
    fix i xs br
    assume "br \<in> {0..<Suc (sum_list (take (Suc i) xs))}"
    show "\<exists>a\<subseteq>set (take (Suc i) xs). br = \<Sum> a"
      sorry
  qed
next
  show "\<And>i xs nadjen.
       i \<le> length xs \<and> (\<forall>br\<in>{0..<Suc (sum_list (take i xs))}. \<exists>a\<subseteq>set (take i xs). br = \<Sum> a) \<and> i < length xs \<and> \<not> nadjen \<Longrightarrow>
       length xs - Suc i < length xs - i" 
    by auto
next
  show "\<And>i xs nadjen.
       i \<le> length xs \<and> (\<forall>br\<in>{0..<Suc (sum_list (take i xs))}. \<exists>a\<subseteq>set (take i xs). br = \<Sum> a) \<and> (i < length xs \<longrightarrow> nadjen) \<Longrightarrow>
       i = length xs \<or> nadjen"
    by auto
qed


end