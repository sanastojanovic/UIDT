
(*<*)
theory Vezbe04_resenja
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Intuicionistička pravila prirodne dedukcije u logici prvog reda]\<close>

text \<open>Diskutovati o pravilima uvođenja i pravilima eliminacije prirodne dedukcije u logici 
      prvog reda. Pomoću ključne reči @{text "thm"} ispitati svako pravilo prirodne dedukcije. 
      Primeniti odgovarajuće pravilo prirodne dedukcije na jednostavnim formulama i diskutovati 
      o cilju koga treba dokazati pre i posle primene tog pravila.\<close>

text \<open>Za logiku prvog reda pored pravila prirodne dedukcije iskazne 
      logike, važe i pravila uvođenja i elimenacije kvantifikatora.\<close>

text \<open>Uvođenje univerzalnog kvantifikatora: \<open>allI\<close>\<close>

thm allI

lemma "\<forall> x. P x"
  apply (rule allI)
  (*<*) oops (*>*)

text \<open>Eliminacija univerzalnog kvantifikatora: \<open>allE\<close>\<close>

thm allE

lemma "\<forall> x. P x \<Longrightarrow> A"
  apply (erule_tac x = "t" in allE)
  (*<*) oops (*>*)

text \<open>Uvođenje egzistencijalnog kvantifikatora: \<open>exI\<close>\<close>

thm exI

lemma "\<exists> x. P x"
  apply (rule_tac x = "t" in exI)
  (*<*) oops (*>*)

text \<open>Eliminacija egzistencijalnog kvantifikatora: \<open>exE\<close>\<close>

thm exE

lemma "\<exists> x. P x \<Longrightarrow> A"
  apply (erule exE)
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule valjane u logici prvog reda. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "(\<forall> x. Man x \<longrightarrow> Mortal x) \<and> Man Socrates \<longrightarrow> Mortal Socrates"
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x = "Socrates" in allE)
  apply (erule impE)
   apply assumption +
  done

lemma de_Morgan_1: "(\<exists> x. \<not> P x) \<longrightarrow> \<not> (\<forall> x. P x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (erule notE)
  apply assumption
  done

lemma de_Morgan_2: "(\<forall> x. \<not> P x) \<longrightarrow> (\<nexists> x. P x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (erule notE)
  apply assumption
  done

lemma de_Morgan_3: "(\<nexists> x. P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x = "x" in exI)
  apply assumption
  done

lemma "(\<exists> x. P x) \<and> (\<forall> x. P x \<longrightarrow> Q x) \<longrightarrow> (\<exists> x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (rule_tac x = "x" in exI)
  apply (erule impE)
   apply assumption +
  done

lemma "(\<forall> m. Man m \<longrightarrow> Mortal m) \<and> 
       (\<forall> g. Greek g \<longrightarrow> Man g) \<longrightarrow>
       (\<forall> a. Greek a \<longrightarrow> Mortal a)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x = "a" in allE) +
  apply (erule impE) +
    apply assumption +
  done

text \<open>Dodatni primeri:\<close>

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x = "x" in allE) +
  apply (erule impE)
   apply assumption +
  done

lemma "(\<exists> x. A x \<or> B x) \<longrightarrow> (\<exists> x. A x) \<or> (\<exists> x. B x)"
  apply (rule impI)
  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule_tac x = "x" in exI)
   apply assumption
  apply (rule disjI2)
  apply (rule_tac x = "x" in exI)
  apply assumption
  done

lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> (\<nexists> x. A x \<and> B x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule_tac x = "x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

text \<open>Formulisati i dokazati naredna tvrđenja.\<close>

text \<open>Ako za svaki broj koji nije paran važi da je neparan;\\
      i ako za svaki neparan broj važi da nije paran;\\
      pokazati da onda za svaki broj važi da nije istovremeno i paran i neparan\<close>

lemma "
    (\<forall> x. \<not> Paran x \<longrightarrow> Neparan x) \<and>
    (\<forall> x. Neparan x \<longrightarrow> \<not> Paran x) \<longrightarrow>
    (\<forall> x. \<not> (Paran x \<and> Neparan x))"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule_tac x = "x" in allE) +
  apply (erule impE) +
    apply assumption +
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

text \<open>Ako svaki konj ima potkovice;\\
      i ako ne postoji čovek koji ima potkovice;\\
      i ako znamo da postoji makar jedan čovek;\\
      dokazati da postoji čovek koji nije konj.\<close>

lemma "(\<forall> x. Konj x \<longrightarrow> Potkovice x) \<and>
       (\<nexists> x. Covek x \<and> Potkovice x) \<and>
       (\<exists> x. Covek x) \<longrightarrow>
       (\<exists> x. Covek x \<and> \<not> Konj x)"
  apply (rule impI)
  apply (erule conjE) +
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (rule_tac x = "x" in exI)
  apply (rule conjI)
   apply assumption
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply (rule_tac x = "x" in exI)
  apply (rule conjI)
   apply assumption +
  done

text \<open>Ako je svaki kvadrat romb;\\
      i ako je svaki kvadrat pravougaonik;\\
      i ako znamo da postoji makar jedan kvadrat;\\
      onda postoji makar jedan romb koji je istovremeno i pravougaonik.\<close>

lemma "(\<forall> x. Kvadrat x \<longrightarrow> Romb x) \<and>
       (\<forall> x. Kvadrat x \<longrightarrow> Pravougaonik x) \<and>
       (\<exists> x. Kvadrat x) \<longrightarrow>
       (\<exists> x. Romb x \<and> Pravougaonik x)"
  apply (rule impI)
  apply (erule conjE) +
  apply (erule exE)
  apply (erule_tac x = "x" in allE) +
  apply (rule_tac x = "x" in exI)
  apply (rule conjI)
   apply (erule impE)
    apply assumption +
  apply (erule impE) +
    apply assumption +
  apply (erule impE)
   apply assumption +
  done

text \<open>Ako je relacija R simetrična, tranzitivna\\
      i ako za svako x postoji y koje je sa njim u relaciji,\\ 
      onda je relacija R i refleksivna.\<close>

text \<open>Savet: Pomoću ključne reči \<open>definition\<close> definisati osobinu refleksivnosti,
      tranzitivnosti i simetricnosti. Ta formulisati tvđenje i dokazati ga.
      Podsetiti se ključne reči \<open>unfolding\<close> za raspisivanje definicije.\<close>

definition "reflexive R \<equiv> \<forall> x. R x x"

definition "transitive R \<equiv> \<forall> x y z. R x y \<and> R y z \<longrightarrow> R x z"

definition "symmetric R \<equiv> \<forall> x y. R x y \<longleftrightarrow> R y x"

lemma "symmetric R \<and> transitive R \<and> 
       (\<forall> x. \<exists> y. R x y) \<longrightarrow> 
       reflexive R"
  unfolding reflexive_def transitive_def symmetric_def
  apply (rule impI)
  apply (erule conjE) +
  apply (rule allI)
  apply (erule_tac x = "x" in allE) back back
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (erule_tac x = "x" in allE)
  apply (erule_tac x = "y" in allE)
  apply (erule_tac x = "y" in allE)
  apply (erule_tac x = "x" in allE)
  apply (erule iffE)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply (erule impE)
    apply assumption +
  done

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: ccontr.]\<close>

text \<open>Diskutovati zašto sledeće tvrđenje može biti dokazano samo intuicionističkim pravilima 
      prirodne dedukcije, dok to ne važi za tvrđenje nakon njega. Primetiti razliku između 
      pravila \<open>notI\<close> i \<open>ccontr\<close>.\<close>

lemma \<open>A \<longrightarrow> \<not> \<not> A\<close>
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

thm notI
thm ccontr

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply assumption
  done

text \<open>Dokazati sledeća tvrđenja:\<close>

lemma "(\<not> P \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule conjI)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not> (\<forall> x. P x)) \<longrightarrow> (\<exists> x. \<not> P x)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule_tac x = "x" in exI)
  apply assumption
  done

text \<open>Dodatni primeri:\<close>

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE) back
  apply assumption
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
  apply (erule notE)
   apply assumption
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule notE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: classical.]\<close>

text \<open>Pokazati naredna tvrđenja pomoću pravila \<open>classical\<close>. Zgodna alternativa ovog pravila je 
      razdvajanje na slučajeve neke podformule.\<close>

thm classical

lemma "P \<or> \<not> P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B)) \<longrightarrow> B"
  apply (rule impI)
  apply (cases A)
   apply (erule iffE)
   apply (erule impE)
    apply assumption
   apply (erule iffE)
   apply (erule impE) back
    apply assumption +
  apply (rule ccontr)
  apply (erule iffE)
  apply (erule impE) back
  apply (rule iffI)
    apply (erule notE)
    apply assumption
   apply (erule impE)
    apply (erule notE) back
    apply assumption
   apply (erule notE) back
   apply assumption
  apply (erule notE)
  apply assumption
  done

text \<open>\<open>Paradoks pijanca\<close>:\\
      Postoji osoba za koju važi, ako je on pijanac onda su i svi ostali pijanci.\<close>

lemma drinker's_paradox: "\<exists> x. drunk x \<longrightarrow> (\<forall> x. drunk x)"
  apply (cases "\<forall> x. drunk x")
   apply (rule exI)
   apply (rule impI)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule_tac x = "x" in exI)
  apply (rule impI)
  apply (erule notE)
  apply assumption
  done

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
