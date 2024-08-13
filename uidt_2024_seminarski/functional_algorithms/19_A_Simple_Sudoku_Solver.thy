theory "19_A_Simple_Sudoku_Solver"
  imports Main

(* Dejana Kop 91/2019 *)

begin

(* ------------------ SPECIFICATION ---------------------- *)

type_synonym 'a Row = "'a list"
type_synonym 'a Matrix = "'a Row list"
type_synonym Digit = "char"
type_synonym Grid = "Digit Matrix"
type_synonym Choices = "Digit list"

(*--------------------------------------*)

definition digits :: "Digit list" where
  "digits \<equiv> ''123456789''"

definition blank :: "Digit \<Rightarrow> bool" where
  "blank c \<equiv> (c = (CHR ''0''))"

value "blank (CHR ''0'')"
value "blank (CHR ''1'')"

(*------------ test grid --------------*)

(*
  Haselbauer, Nathan [2005] 
  The Mammoth Book of Sudoku
  Puzzle No 61:
  
  -- Zbog slozenosti expand funkcije, 
     na slabijim racunarima se desava 
     da program prekine izvrsavanje na
     originalnoj resetki. Zbog toga 
     ostavljam i delimicno resenu 
     resetku kao test primer.
*)

definition testGridOriginal :: "Grid" where
  "testGridOriginal = [
    ''009150600'',
    ''346000152'', 
    ''081200040'',

    ''060008900'',
    ''100403006'',
    ''005700020'',

    ''030009070'',
    ''917000263'',
    ''008072400''
   ]"

definition testGrid :: "Grid" where
  "testGrid = [
    ''029154638'',
    ''346980152'', 
    ''581236749'',

    ''463528917'',
    ''172403586'',
    ''895760324'',

    ''234619875'',
    ''917845263'',
    ''658372491''
   ]"

(*------------ choices ----------------*)

definition choice :: "Digit \<Rightarrow> Choices" where 
  "choice d = (
    if blank d 
      then digits 
    else 
      [d]
  )"

value "choice (CHR ''0'')"
value "choice (CHR ''1'')"

definition choices :: "Grid \<Rightarrow> Choices Matrix"  where 
  "choices = map (map choice)"

value "choices testGrid"

(*------------- expand ----------------*)

fun cp :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "cp [] = [[]]"
| "cp (xs # xss) = [(x # ys) . x <- xs, ys <- cp xss]"

value "cp [''12'', ''3'', ''45'']"

definition expand :: "Choices Matrix \<Rightarrow> Grid list"  where 
  "expand = cp \<circ> map cp"

value "expand (choices testGrid)"

(*-------------- valid ----------------*)

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "all p [] = True"
| "all p (x # xs) = ((p x) \<and> (all p xs))"

fun check :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "check x [] = True"
| "check x (xx # xs) = ((x \<noteq> xx) \<and> (check x xs))"

fun nodups :: "'a list \<Rightarrow> bool" where 
  "nodups [] = True"
| "nodups (x # xs) = ((check x xs) \<and> (nodups xs))"

value "nodups ''0123456789''"
value "nodups ''0123456781''"

definition rows :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "rows = id"

value "rows testGrid"

fun cols :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "cols [] = []"
| "cols [xs] = [[x] . x <- xs]"
| "cols (xs # xss) = map2 (Cons) xs (cols xss)"

value "cols testGrid"

fun group :: "'a list \<Rightarrow> 'a Matrix" where
  "group [] = []"
| "group xs = take 3 xs # group (drop 3 xs)"

definition ungroup :: "'a Matrix \<Rightarrow> 'a list" where
  "ungroup = concat"

value "ungroup testGrid"
value "group (ungroup testGrid)"

definition boxs :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "boxs = map ungroup \<circ> ungroup \<circ> map cols \<circ> group \<circ> map group"

value "boxs testGrid"

definition valid :: "Grid \<Rightarrow> bool" where
  "valid g \<equiv>
    (all nodups (rows g)) \<and> 
    (all nodups (cols g)) \<and>
    (all nodups (boxs g))
  "

value "valid testGrid" 
(* False zbog ponavljanja 0 za prazna polja *)

(*--------------- solve ----------------*)

definition solve :: "Grid \<Rightarrow> Grid list" where
  "solve = filter valid \<circ> expand \<circ> choices"

value "solve testGrid"

(*--------------- lemmas ---------------*)

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

(* --------------------- PRUNING ------------------------- *)

definition singleton :: "'a list \<Rightarrow> bool" where
  "singleton l = (if length l = 1 then True else False)"

value "singleton ''''"
value "singleton ''1''"
value "singleton ''12''"

definition remove :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "remove xs ds = (
    if singleton ds 
      then ds 
    else 
      filter (\<lambda> d . \<not> (d \<in> set xs)) ds
    )
  "

value "remove '''' ''12345''"
value "remove ''1'' ''12345''"
value "remove ''6'' ''12345''"

definition fixed :: "Choices Row \<Rightarrow> Choices" where 
  "fixed row = [d . [d] <- row]"

value "fixed (hd (choices testGridOriginal))"

definition pruneRow :: "Choices Row \<Rightarrow> Choices Row" where 
  "pruneRow row = map (remove (fixed row)) row"

value "pruneRow (hd (choices testGridOriginal))"

lemma "19_4": "filter nodups \<circ> cp = filter nodups \<circ> cp \<circ> pruneRow"
  sorry

lemma "19_5":
  assumes "f \<circ> f = id"
  shows "filter (p \<circ> f) = map f \<circ> filter p \<circ> map f"
  sorry

lemma "19_5_1":
  assumes "f \<circ> f = id"
  shows "filter (p \<circ> f) \<circ> map f = map f \<circ> filter p"
  sorry

lemma "19_6": "filter (all p) \<circ> cp = cp \<circ> map (filter p)"
  sorry

definition pruneBy :: "(Choices Matrix \<Rightarrow> Choices Matrix) \<Rightarrow> Choices Matrix \<Rightarrow> Choices Matrix" where 
  "pruneBy f = f \<circ> map pruneRow \<circ> f"

value "pruneBy rows (choices testGridOriginal)"
value "pruneBy cols (choices testGridOriginal)"
value "pruneBy boxs (choices testGridOriginal)"

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

value "prune (choices testGridOriginal)"

lemma prunning: "filter valid \<circ> expand = filter valid \<circ> expand \<circ> prune"
  sorry

lemma solve_prune: "solve = filter valid \<circ> expand \<circ> prune \<circ> choices"
  sorry

definition solve2 :: "Grid \<Rightarrow> Grid list" where 
  "solve2 = filter valid \<circ> expand \<circ> prune \<circ> choices"

value "solve2 testGrid"

(* ---------------- SINGLE-CELL EXPANSION ---------------- *)

definition counts :: "Choices Matrix \<Rightarrow> nat list" where 
  "counts = filter (\<lambda> x. x \<noteq> 1) \<circ> map length \<circ> concat"

value "counts [[''2'', ''34'', ''567''], [''2'', ''3'', ''56789'']]"

definition break :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list)*('a list)" where
  "break p xs = (takeWhile (\<lambda> x. \<not> (p x)) xs, dropWhile (\<lambda> x. \<not> (p x)) xs)"

value "break (\<lambda> x. x = (CHR ''4'')) ''123456789''"

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

value "expand1 (choices testGridOriginal)"

lemma "19_7_expand1_property": "expand = concat \<circ> map expand \<circ> expand1"
  sorry

definition complete :: "Choices Matrix \<Rightarrow> bool" where
  "complete = all (all singleton)"

value "complete [[''1'', ''1'', ''1''],[''1'', ''1'', '''']]"
value "complete [[''1'', ''1'', ''1''],[''1'', ''1'', ''1'']]"
value "complete [[''1'', ''12'', ''1''],[''1'', ''145'', ''1'']]"

fun all_list :: "(Choices Row \<Rightarrow> bool) \<Rightarrow> Choices Matrix \<Rightarrow> bool" where 
  "all_list p [] = True"
| "all_list p (xs # xss) = ((p xs) \<and> (all p xss))"

definition ok :: "Choices Row \<Rightarrow> bool" where
  "ok row = nodups [d. [d] <- row]"

definition safe :: "Choices Matrix \<Rightarrow> bool" where
  "safe m = (
    all_list ok (rows m) \<and> 
    all_list ok (cols m) \<and> 
    all_list ok (boxs m)
  )"

lemma sce1: 
  fixes m :: "Choices Matrix"
  assumes "(safe m) \<and> \<not>(complete m)"
  shows "filter valid (expand m) = concat (map (filter valid \<circ> expand \<circ> prune) (expand1 m))"
  sorry

definition search :: "Choices Matrix \<Rightarrow> Grid list" where 
  "search = filter valid \<circ> expand \<circ> prune"

lemma sce2:
  fixes m :: "Choices Matrix"
  assumes "(safe m) \<and> \<not>(complete m)"
  shows "search (prune m) = concat (map search (expand1 m))"
  sorry

definition search1 :: "Choices Matrix \<Rightarrow> Choices Matrix"  where
  "search1 m = (
    if \<not> safe m 
      then [] 
    else (
      if complete (prune m) 
        then [map (map hd) (prune m)] 
      else concat (map search (expand1 (prune m)))
    )
  )"

value "search1 (choices testGridOriginal)"

definition solve3 :: "Grid \<Rightarrow> Grid list" where 
  "solve3 = search1 \<circ> choices"

value "solve3 testGridOriginal"

end