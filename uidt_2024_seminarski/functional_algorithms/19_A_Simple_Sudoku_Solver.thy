theory "19_A_Simple_Sudoku_Solver"
  imports Main

(* Dejana Kop 91/2019 *)

begin

type_synonym 'a Row = "'a list"
type_synonym 'a Matrix = "'a Row list"
type_synonym Digit = "char"
type_synonym Grid = "Digit Matrix"
type_synonym Choices = "Digit list"

definition digits :: "Digit list" where
  "digits \<equiv> ''123456789''"

definition blank :: "Digit \<Rightarrow> bool" where
  "blank c \<equiv> (c = (CHR ''0''))"

(* CHOICES *)

definition choice :: "Digit \<Rightarrow> Choices" where 
  "choice d = (if blank d then digits else [d])"

definition choices :: "Grid \<Rightarrow> Choices Matrix"  where 
  "choices = map (map choice)"

(* EXPAND *)

fun cp :: "'a list list \<Rightarrow> 'a list list" where 
  "cp [] = [[]]"
| "cp (xs # xss) = [(x # ys) . x <- xs, ys <- cp xss]"

value "cp [''12'', ''3'', ''45'']"

definition expand :: "Choices Matrix \<Rightarrow> Grid list"  where 
  "expand = cp \<circ> map cp"

(* VALID *)

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "all p [] = True"
| "all p (x # xs) = ((p x) \<and> (all p xs))"

fun check :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "check x [] = True"
| "check x (xx # xs) = ((x = xx) \<and> (check x xs))"

fun nodups :: "'a Row \<Rightarrow> bool" where 
  "nodups [] = True"
| "nodups (x # xs) = ((check x xs) \<and> (nodups xs))"

definition rows :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "rows = id"

fun cols :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "cols [] = []"
| "cols [xs] = [[x] . x <- xs]"
| "cols (xs # xss) = map2 (Cons) xs (cols xss)"

fun group :: "'a list \<Rightarrow> 'a Matrix" where
  "group [] = []"
| "group xs = take 3 xs # group (drop 3 xs)"

definition ungroup :: "'a Matrix \<Rightarrow> 'a list" where
  "ungroup = concat"

definition boxs :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "boxs = map ungroup \<circ> ungroup \<circ> map cols \<circ> group \<circ> map group"

definition valid :: "Grid \<Rightarrow> bool" where
  "valid g \<equiv>
    (all nodups (rows g)) \<and> 
    (all nodups (cols g)) \<and>
    (all nodups (boxs g))
  "

(* SOLVE *)

definition solve :: "Grid \<Rightarrow> Grid list" where 
  "solve = filter valid \<circ> expand \<circ> choices"

(* LEMMAS *)

lemma group_ungroup: "group \<circ> ungroup = id"
  sorry

lemma rows_id: "rows \<circ> rows = id"
  sorry

lemma cols_id: "cols \<circ> cols = id"
  sorry

lemma boxs_id: "boxs \<circ> boxs = id"
  sorry

lemma "19_1_expand_rows": "map rows \<circ> expand = expand \<circ> rows"
  sorry

lemma "19_2_expand_cols": "map cols \<circ> expand = expand \<circ> cols"
  sorry

lemma "19_3_expand_boxs": "map boxs \<circ> expand = expand \<circ> boxs"
  sorry

(* PRUNING *)

definition singleton :: "'a list \<Rightarrow> bool" where
  "singleton l = (if length l = 1 then True else False)"

definition remove :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "remove xs ds = (if singleton ds then ds else (filter (\<lambda> d . \<not> (d \<in> set xs))) ds)"

definition fixed :: "Choices Row \<Rightarrow> Choices" where 
  "fixed row = [d . [d] <- row]"

definition pruneRow :: "Choices Row \<Rightarrow> Choices Row" where 
  "pruneRow row = map (remove (fixed row)) row"

lemma "19_4_nodups_cp_pruneRow": "filter nodups \<circ> cp = filter nodups \<circ> cp \<circ> pruneRow"
  sorry

lemma "19_5_filter1":
  assumes "f \<circ> f = id"
  shows "filter (p \<circ> f) = map f \<circ> filter p \<circ> map f"
  sorry

lemma filter2:
  assumes "f \<circ> f = id"
  shows "filter (p \<circ> f) \<circ> map f = map f \<circ> filter p"
  sorry

lemma "19_6_filter3": "filter (all p) \<circ> cp = cp \<circ> map (filter p)"
  sorry

definition pruneBy where 
  "pruneBy f = f \<circ> map pruneRow \<circ> f"

lemma filter_valid_expand: 
  "filter valid \<circ> expand = 
    filter (all nodups \<circ> boxs) \<circ>
    filter (all nodups \<circ> cols) \<circ>
    filter (all nodups \<circ> rows) \<circ> expand
  "
  sorry

lemma prune_by_boxs: 
  "filter (all nodups \<circ> boxs) \<circ> expand 
    = filter (all nodups \<circ> boxs) \<circ> expand \<circ> pruneBy boxs"
  sorry

lemma prune_by_rows: 
  "filter (all nodups \<circ> rows) \<circ> expand 
    = filter (all nodups \<circ> rows) \<circ> expand \<circ> pruneBy rows"
  sorry

lemma prune_by_cols: 
  "filter (all nodups \<circ> cols) \<circ> expand 
    = filter (all nodups \<circ> cols) \<circ> expand \<circ> pruneBy cols"
  sorry

definition prune :: "Choices Matrix \<Rightarrow> Choices Matrix" where
  "prune = pruneBy boxs \<circ> pruneBy cols \<circ> pruneBy rows"

lemma prune1: "filter valid \<circ> expand = filter valid \<circ> expand \<circ> prune"
  sorry

lemma solve_prune: "solve = filter valid \<circ> expand \<circ> prune \<circ> choices"
  sorry

definition solve2 :: "Grid \<Rightarrow> Grid list" where 
  "solve2 = filter valid \<circ> expand \<circ> prune \<circ> choices"

(* SINGLE-CELL EXPANSION *)

definition counts :: "Choices Matrix \<Rightarrow> nat list" where 
  "counts = filter (\<lambda> x. x \<noteq> 1) \<circ> map length \<circ> concat"

definition break :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list)*('a list)" where
  "break p xs = (takeWhile (\<lambda> x. \<not> (p x)) xs, dropWhile (\<lambda> x. \<not> (p x)) xs)"

definition expand1 :: "Choices Matrix \<Rightarrow> Choices Matrix list" where
  "expand1 rowsArg \<equiv>
    (let
      n = min_list (counts rowsArg);
      (rows1, rest1) = break (\<lambda> r. \<exists> x \<in> set r. length x = n) rowsArg;
      row = hd rest1;
      rows2 = tl rest1;
      (row1, rest2) = break (\<lambda> r. length r = n) row;
      cs = hd rest2;
      row2 = tl rest2
    in
      [rows1 @ [row1 @ ([c] # row2)] @ rows2 . c <- cs]
    )
  "

lemma "19_7_expand1_property": "expand = concat \<circ> map expand \<circ> expand1"
  sorry

(* TESTS *)

definition complete :: "Choices Matrix \<Rightarrow> bool" where
  "complete = all (all singleton)"

fun all_list :: "(Choices Row \<Rightarrow> bool) \<Rightarrow> Choices Matrix \<Rightarrow> bool" where 
  "all_list p [] = True"
| "all_list p (xs # xss) = ((p xs) \<and> (all p xss))"

definition ok :: "Choices Row \<Rightarrow> bool" where
  "ok row = nodups [d. [d] <- row]"

definition safe :: "Choices Matrix \<Rightarrow> bool" where
  "safe m = (all_list ok (rows m) \<and> all_list ok (cols m) \<and> all_list ok (boxs m))"

lemma *: 
  fixes m :: "Choices Matrix"
  assumes "(safe m) \<and> \<not>(complete m)"
  shows "filter valid \<circ> expand = concat \<circ> map (filter valid \<circ> expand \<circ> prune) \<circ> expand1"
  sorry

definition search :: "Choices Matrix \<Rightarrow> Choices Matrix" where 
  "search = filter valid \<circ> expand \<circ> prune"

definition search1 :: "Choices Matrix \<Rightarrow> Choices Matrix"  where
  "search1 m = (if \<not> safe m then [] 
               else (if complete (prune m) then [map (map hd) (prune m)] 
                     else concat (map search (expand1 (prune m)))))"

lemma **:
  fixes m :: "Choices Matrix"
  assumes "(safe m) \<and> \<not>(complete m)"
  shows "search1 \<circ> prune = concat \<circ> map search \<circ> expand1"
  sorry

definition solve3 :: "Grid \<Rightarrow> Grid list" where "solve3 = search \<circ> choices"

end