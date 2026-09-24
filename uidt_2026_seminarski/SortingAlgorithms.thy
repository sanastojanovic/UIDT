theory SortingAlgorithms
imports
  Main "HOL-Library.Multiset"
begin

hide_const List.insort

declare Let_def [simp]


subsection "Insertion Sort"

fun insort :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insort x [] = [x]" |
"insort x (y#ys) =
  (if x \<le> y then x#y#ys else y#(insort x ys))"

fun isort :: "'a::linorder list \<Rightarrow> 'a list" where
"isort [] = []" |
"isort (x#xs) = insort x (isort xs)"



lemma mset_insort: "mset (insort x xs) = {#x#} + mset xs"
apply(induction xs)
apply auto
done

lemma mset_isort: "mset (isort xs) = mset xs"
apply(induction xs)
apply simp
apply (simp add: mset_insort)
done

lemma set_insort: "set (insort x xs) = {x} \<union> set xs"
by(simp add: mset_insort flip: set_mset_mset)

lemma sorted_insort: "sorted (insort a xs) = sorted xs"
apply(induction xs)
apply(auto simp add: set_insort)
done

lemma sorted_isort: "sorted (isort xs)"
apply(induction xs)
apply(auto simp: sorted_insort)
done



subsection "Merge Sort"

fun merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"merge [] ys = ys" |
"merge xs [] = xs" |
"merge (x#xs) (y#ys) = (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"

fun msort :: "'a::linorder list \<Rightarrow> 'a list" where
"msort xs = (let n = length xs in
  if n \<le> 1 then xs
  else merge (msort (take (n div 2) xs)) (msort (drop (n div 2) xs)))"

declare msort.simps [simp del]



lemma mset_merge: "mset(merge xs ys) = mset xs + mset ys"
by(induction xs ys rule: merge.induct) auto

lemma mset_msort: "mset (msort xs) = mset xs"
proof(induction xs rule: msort.induct)
  case (1 xs)
  let ?n = "length xs"
  let ?ys = "take (?n div 2) xs"
  let ?zs = "drop (?n div 2) xs"
  show ?case
  proof cases
    assume "?n \<le> 1"
    thus ?thesis by(simp add: msort.simps[of xs])
  next
    assume "\<not> ?n \<le> 1"
    hence "mset (msort xs) = mset (msort ?ys) + mset (msort ?zs)"
      by(simp add: msort.simps[of xs] mset_merge)
    also have "\<dots> = mset ?ys + mset ?zs"
      using \<open>\<not> ?n \<le> 1\<close> by(simp add: "1.IH")
    also have "\<dots> = mset (?ys @ ?zs)" by (simp del: append_take_drop_id)
    also have "\<dots> = mset xs" by simp
    finally show ?thesis .
  qed
qed



lemma set_merge: "set(merge xs ys) = set xs \<union> set ys"
by (metis mset_merge set_mset_mset set_mset_union)

lemma "set(merge xs ys) = set xs \<union> set ys"
by(induction xs ys rule: merge.induct) (auto)

lemma sorted_merge: "sorted (merge xs ys) \<longleftrightarrow> (sorted xs \<and> sorted ys)"
by(induction xs ys rule: merge.induct) (auto simp: set_merge)

lemma sorted_msort: "sorted (msort xs)"
proof(induction xs rule: msort.induct)
  case (1 xs)
  let ?n = "length xs"
  show ?case
  proof cases
    assume "?n \<le> 1"
    thus ?thesis by(simp add: msort.simps[of xs] sorted01)
  next
    assume "\<not> ?n \<le> 1"
    thus ?thesis using "1.IH"
      by(simp add: sorted_merge msort.simps[of xs])
  qed
qed

subsection "Quicksort"

fun quicksort :: "('a::linorder) list \<Rightarrow> 'a list" where
"quicksort []     = []" |
"quicksort (x#xs) = quicksort (filter (\<lambda>y. y < x) xs) @ [x] @ quicksort (filter (\<lambda>y. x \<le> y) xs)"

lemma mset_quicksort: "mset (quicksort xs) = mset xs"
apply (induction xs rule: quicksort.induct)
apply (auto simp: not_le)
done

lemma set_quicksort: "set (quicksort xs) = set xs"
by(rule mset_eq_setD[OF mset_quicksort])

lemma sorted_quicksort: "sorted (quicksort xs)"
apply (induction xs rule: quicksort.induct)
apply (auto simp add: sorted_append set_quicksort)
  done
