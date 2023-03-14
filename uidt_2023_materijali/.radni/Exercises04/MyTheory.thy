
(*<*)
theory MyTheory
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

lemma "\<forall> x. P x"
  (*<*) oops (*>*)

text \<open>Eliminacija univerzalnog kvantifikatora: \<open>allE\<close>\<close>

lemma "\<forall> x. P x \<Longrightarrow> A"
  (*<*) oops (*>*)

text \<open>Uvođenje egzistencijalnog kvantifikatora: \<open>exI\<close>\<close>

lemma "\<exists> x. P x"
  (*<*) oops (*>*)

text \<open>Eliminacija egzistencijalnog kvantifikatora: \<open>exE\<close>\<close>

lemma "\<exists> x. P x \<Longrightarrow> A"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule valjane u logici prvog reda. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "(\<forall> x. Man x \<longrightarrow> Mortal x) \<and> Man Socrates \<longrightarrow> Mortal Socrates"
  (*<*) oops (*>*)

lemma de_Morgan_1: "(\<exists> x. \<not> P x) \<longrightarrow> \<not> (\<forall> x. P x)"
  (*<*) oops (*>*)

lemma de_Morgan_2: "(\<forall> x. \<not> P x) \<longrightarrow> (\<nexists> x. P x)"
  (*<*) oops (*>*)

lemma de_Morgan_3: "(\<nexists> x. P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  (*<*) oops (*>*)

lemma "(\<exists> x. P x) \<and> (\<forall> x. P x \<longrightarrow> Q x) \<longrightarrow> (\<exists> x. Q x)"
  (*<*) oops (*>*)

lemma "(\<forall> m. Man m \<longrightarrow> Mortal m) \<and> 
       (\<forall> g. Greek g \<longrightarrow> Man g) \<longrightarrow>
       (\<forall> a. Greek a \<longrightarrow> Mortal a)"
  (*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x. Q x)"
  (*<*) oops (*>*)

lemma "(\<exists> x. A x \<or> B x) \<longrightarrow> (\<exists> x. A x) \<or> (\<exists> x. B x)"
  (*<*) oops (*>*)

lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> (\<nexists> x. A x \<and> B x)"
  (*<*) oops (*>*)

text \<open>Formulisati i dokazati naredna tvrđenja.\<close>

text \<open>Ako za svaki broj koji nije paran važi da je neparan;\\
      i ako za svaki neparan broj važi da nije paran;\\
      pokazati da onda za svaki broj važi da nije istovremeno i paran i neparan.\<close>

text \<open>Ako je svaki kvadrat romb;\\
      i ako je svaki kvadrat pravougaonik;\\
      i ako znamo da postoji makar jedan kvadrat;\\
      onda postoji makar jedan romb koji je istovremeno i pravougaonik.\<close>

text \<open>Ako je relacija R simetrična, tranzitivna\\
      i ako za svako x postoji y koje je sa njim u relaciji,\\ 
      onda je relacija R i refleksivna.\<close>

text \<open>Savet: Pomoću ključne reči \<open>definition\<close> definisati osobinu refleksivnosti,
      tranzitivnosti i simetricnosti. Ta formulisati tvđenje i dokazati ga.
      Podsetiti se ključne reči \<open>unfolding\<close> za raspisivanje definicije.\<close>

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: ccontr.]\<close>

text \<open>Diskutovati zašto sledeće tvrđenje može biti dokazano samo intuicionističkim pravilima 
      prirodne dedukcije, dok to ne važi za tvrđenje nakon njega. Primetiti razliku između 
      pravila \<open>notI\<close> i \<open>ccontr\<close>.\<close>

lemma \<open>A \<longrightarrow> \<not> \<not> A\<close>
  (*<*) oops (*>*)

lemma "\<not> \<not> A \<longrightarrow> A"
  (*<*) oops (*>*)

text \<open>Dokazati sledeća tvrđenja:\<close>

lemma "(\<not> P \<longrightarrow> P) \<longrightarrow> P"
  (*<*) oops (*>*)

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  (*<*) oops (*>*)

lemma "(\<not> (\<forall> x. P x)) \<longrightarrow> (\<exists> x. \<not> P x)"
  (*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  (*<*) oops (*>*)

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  (*<*) oops (*>*)

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: classical.]\<close>

text \<open>Pokazati naredna tvrđenja pomoću pravila \<open>classical\<close>. Zgodna alternativa ovog pravila je 
      razdvajanje na slučajeve neke podformule.\<close>

thm classical

lemma "P \<or> \<not> P"
  (*<*) oops (*>*)

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B)) \<longrightarrow> B"
  (*<*) oops (*>*)

text \<open>\<open>Paradoks pijanca\<close>:\\
      Postoji osoba za koju važi, ako je on pijanac onda su i svi ostali pijanci.\<close>

lemma drinker's_paradox: "\<exists> x. drunk x \<longrightarrow> (\<forall> x. drunk x)"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
