theory Trimini
  imports Main
begin
(*declare [[show_types]] *)
(*
Tvrdjenje koje bi moglo da se dokaze je da za svaku tablu dimenzija 2^n x 2^n
kojoj nedostaje jedno polje postoji ispravno trimini poplocavanje

*)


datatype Orientation = NW | NE | SW | SE
datatype Quadrant = I | II | III | IV

(*Trimini posmatramo kao strelice koje su usmerene prema
stranama sveta, koordina su koodinate spica strelice *)
type_synonym Tromino = "nat * nat * Orientation"
type_synonym Hole = "nat * nat"

fun pow2 :: "nat \<Rightarrow> nat" where
  "pow2 n = 2 ^ n"

fun translate_one :: "(nat * nat) \<Rightarrow> Tromino \<Rightarrow> Tromino" where
  "translate_one (dx, dy) (x, y, orient) = (x + dx, y + dy, orient)"

fun translate :: "(nat * nat) \<Rightarrow> Tromino list \<Rightarrow> Tromino list" where
  "translate delta ts = map (translate_one delta) ts"

fun base_case :: "Hole \<Rightarrow> Tromino list" where
  "base_case (0,0) = [(1, 1, SE)]" |
  "base_case (0,Suc 0) = [(1, 0, NE)]" |
  "base_case (Suc 0,0) = [(0, 1, SW)]" |
  "base_case (Suc 0,Suc 0) = [(0, 0, NW)]"



fun where_is_the_hole :: "nat \<Rightarrow> Hole \<Rightarrow> Quadrant" where
  "where_is_the_hole s (x,y) =
     (let half = s div 2 in
      if x < half \<and> y < half then I
      else if x < half \<and> y \<ge> half then II
      else if x \<ge> half \<and> y \<ge> half then III
      else IV)"

fun center :: "nat \<Rightarrow> Hole \<Rightarrow> Tromino list" where
  "center s hole =
     (if s = 2 then base_case hole
      else
        (let half = s div 2 in
         case where_is_the_hole s hole of
           I \<Rightarrow> [(half, half, SE)] |
           II \<Rightarrow> [(half, half - 1, NE)] |
           III \<Rightarrow> [(half - 1, half - 1, NW)] |
           IV \<Rightarrow> [(half - 1, half, SW)]))"

fun new_holes :: "nat \<Rightarrow> Hole \<Rightarrow> Hole list" where
  "new_holes s hole =
     (case hd (center s hole) of
        (x, y, NW) \<Rightarrow> [(x, y), (x, y + 1), hole, (x + 1, y)] |
        (x, y, NE) \<Rightarrow> [(x - 1, y), hole, (x, y + 1), (x, y)] |
        (x, y, SW) \<Rightarrow> [(x, y - 1), (x, y), (x + 1, y), hole] |
        (x, y, SE) \<Rightarrow> [hole, (x - 1, y), (x, y), (x, y - 1)])"

fun recursion_holes :: "nat \<Rightarrow> Hole list \<Rightarrow> Hole list" where
  "recursion_holes s [(x1,y1), (x2,y2), (x3,y3), (x4,y4)] =
      [(x1,y1),
       (x2, y2 - s div 2),
       (x3 - s div 2, y3 - s div 2),
       (x4 - s div 2, y4)]" |
  "recursion_holes _ _ =  [] " (* ovo sam dodao jer mi se bunio da nema patern za neke slucaje*)


fun tile :: "nat \<Rightarrow> Hole \<Rightarrow> Tromino list" where
  "tile 0 hole = []" |
  "tile (Suc 0) hole = base_case hole" |
  "tile n hole =
    (let size = pow2 n;
         center_tromino = center size hole;
         holes = new_holes size hole;
         rec_hole = recursion_holes size holes;
         prvi = tile (n - 1) (rec_hole ! 0);
         drugi = translate (0, size div 2) (tile (n - 1) (rec_hole ! 1));
         treci = translate (size div 2, size div 2) (tile (n - 1) (rec_hole ! 2));
         cetvrti = translate (size div 2, 0) (tile (n - 1) (rec_hole ! 3))
     in center_tromino @ prvi @ drugi @ treci @ cetvrti)"


value "tile 3 (3,5)" (*Ovo je primer iz aisp skripte*)

fun board_cells :: "nat \<Rightarrow> (nat \<times> nat) set" where
  "board_cells n = {(i, j). i < pow2 n \<and> j < pow2 n}"


fun cells_of_tromino :: "Tromino \<Rightarrow> (nat \<times> nat) set" where
  "cells_of_tromino (x, y, NW) = {(x, y), (x+1, y), (x, y+1)}" |
  "cells_of_tromino (x, y, NE) = {(x, y), (x-1, y), (x, y+1)}" |
  "cells_of_tromino (x, y, SW) = {(x, y), (x, y-1), (x+1, y)}" |
  "cells_of_tromino (x, y, SE) = {(x, y), (x-1, y), (x, y-1)}"


fun valid_tromino :: "nat \<Rightarrow> Tromino \<Rightarrow> bool" where
  "valid_tromino n t \<longleftrightarrow> cells_of_tromino t \<subseteq> board_cells n"

fun valid_tiling :: "nat \<Rightarrow> Tromino list \<Rightarrow> bool" where
  "valid_tiling n ts \<longleftrightarrow> (\<forall>t \<in> set ts. valid_tromino n t) \<and>
   (\<forall> x  \<in> set ts. \<forall>y \<in> set ts. x\<noteq>y \<longrightarrow>  cells_of_tromino x \<inter> cells_of_tromino y = {})"

fun valid_hole :: "nat \<Rightarrow> Hole \<Rightarrow> bool" where
  "valid_hole n (x, y) \<longleftrightarrow> ( x < pow2 n \<and> y < pow2 n)"

fun valid_holes :: "nat \<Rightarrow> Hole list \<Rightarrow> bool" where
"valid_holes n hs \<longleftrightarrow> (\<forall>h \<in> set hs. valid_hole n h)"

lemma "valid_hole 0 (0,0)"
  by simp

lemma "valid_hole 1 (0,0)"
  by simp
lemma "valid_hole 1 (1,0)"
  by simp
lemma "valid_hole 1 (1,1)"
  by simp
lemma "valid_hole 1 (0,1)"
  by simp
lemma unvalid_holes:
" x > 1 \<or>  y > 1  \<Longrightarrow> \<not>valid_hole 1 (x,y)"
  by auto
lemma valid_1_holes:
"x \<le> 1 \<and> y \<le> 1 \<and> n = 1 \<Longrightarrow> valid_hole n (x,y)"
  by auto

lemma center_returns_inside_board:
  assumes "valid_hole n h" "n > 0"
  shows "\<forall>(x, y, orient) \<in> set (center n h). x < pow2 n \<and> y < pow2 n"
  sorry










lemma new_holes_are_valid:
  assumes "valid_hole n h" "n>0"
  shows "valid_holes n (new_holes n h)"
  sorry

lemma recursion_holes_are_valid:
  assumes "valid_holes n hs" "n>0"
  shows "valid_holes n (recursion_holes n hs)"
  sorry





value "valid_hole 3 (3,5)"    (* True *)
value "valid_hole 2 (4,0)"    (* False — x = 8 je van granica *)
value "valid_hole 4 (24,1)"   (* False — negativna koordinata *)


(* 
Za svako n i  svaku tablu dimenzija 2^n x 2^n i bilo koju ispravnu rupu postoji
validno trimini poplocavanje
*)

lemma 
  assumes "valid_hole n h"
  shows "valid_tiling n (tile n h)"
  using assms
proof (induction n h rule: tile.induct)
  case (1 hole)
  then show ?case by auto
next
  case (2 hole)
  then show ?case
  proof (cases "hole = (0,0)")
    case True
    from True show ?thesis by simp
  next
    case False
    then show ?thesis
    proof(cases "hole = (1,0)")
      case True
      then show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (cases "hole = (0,1)")
        case True
        then show ?thesis by simp
      next
        case False
        then show ?thesis
        proof (cases "hole = (1,1)")
          case True
          then show ?thesis by simp
        next
          case False
          with \<open>hole \<noteq> (0,1)\<close> \<open>hole \<noteq> (0,0)\<close> \<open>hole \<noteq> (1,0)\<close> show ?thesis using unvalid_holes
            by (metis "2" One_nat_def less_Suc0 nat_neq_iff valid_hole.elims(2))
        qed
      qed
    qed
  qed
next
  case (3 va hole)
  then show ?case sorry
qed













lemma pow2_positive:
  shows "pow2 n > 0"
  by induction auto

lemma translate_preserves_length:
  "length (translate d ts) = length ts"
  by auto


lemma center_length_1:
  "length (center s hole) = 1"
  sorry



















end

