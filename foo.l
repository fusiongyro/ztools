%{
#include <stdio.h>
%}

%option noyywrap
%x Z

%%

^\%\%Z { BEGIN(Z); }
<Z>^\%\% { BEGIN(INITIAL); }
. { printf("%s", yytext); }

^\+\.\.\n { printf("│ "); BEGIN(Z); }
<Z>^-\.\. { BEGIN(INITIAL); }
<Z>^\|--\n { printf("├────────────\n"); }

^\+-- { printf("┌─── "); BEGIN(Z); }
<Z>^---\n { printf("└──────────────────────────────────────────────────────"); BEGIN(INITIAL); }

<Z>Delta { printf("∆"); }
<Z>Xi { printf("Ξ"); }
<Z>theta { printf("θ"); }
<Z>lambda { printf("λ"); }
<Z>mu { printf("μ"); }
<Z>arithmos { printf("𝔸"); }
<Z>N { printf("ℕ"); }
<Z>P { printf("ℙ"); }
<Z>\/^ { printf("↗"); }
<Z>v\/ { printf("↙"); }
<Z>\\v { printf("↘"); }
<Z>^\\ { printf("↖"); }
<Z>\<\< { printf("《"); }
<Z>>> { printf("》"); }
<Z>\<\| { printf("⦉"); }
<Z>\|> { printf("⦊"); }
<Z>\|- { printf("⊢"); }
<Z>\/\\ { printf("∧"); }
<Z>\/ { printf("∨"); }
<Z>==> { printf("⇒"); }
<Z>\<=> { printf("⇔"); }
<Z>not { printf("¬"); }
<Z>A { printf("∀"); }
<Z>E { printf("∃"); }
<Z>x { printf("×"); }
<Z>e { printf("∈"); }
<Z>@ { printf("⦁"); }
<Z>S\\ { printf("⧹"); }
<Z>S\|\\ { printf("⨡"); }
<Z>S\; { printf("⨟"); }
<Z>S>> { printf("⨠"); }
<Z>\<--> { printf("↔"); }
<Z>--> { printf("→"); }
<Z>\/= { printf("≠"); }
<Z>\/e { printf("∉"); }
<Z>\(\/\) { printf("∅"); }
<Z>c_ { printf("⊆"); }
<Z>c { printf("⊂"); }
<Z>u { printf("∪"); }
<Z>n { printf("∩"); }
<Z>(-) { printf("⊖"); }
<Z>uu { printf("⋃"); }
<Z>nn { printf("⋂"); }
<Z>F { printf("𝔽"); }
<Z>\|--> { printf("↦"); }
<Z>\; { printf("⨾"); }
<Z>o { printf("∘"); }
<Z>\<: { printf("◁"); }
<Z>:> { printf("▷"); }
<Z>\<-: { printf("⩤"); }
<Z>:-> { printf("⩥"); }
<Z>~ { printf("∼"); }
<Z>\(\| { printf("⦇"); }
<Z>\|\) { printf("⦈"); }
<Z>\(\+\) { printf("⊕"); }
<Z>-\|-> { printf("⇸"); }
<Z>>-\|-> { printf("⤔"); }
<Z>>--> { printf("↣"); }
<Z>-\|->> { printf("⤀"); }
<Z>-->> { printf("↠"); }
<Z>>-->> { printf("⤖"); }
<Z>-\|\|-> { printf("⇻"); }
<Z>>-\|\|-> { printf("⤕"); }
<Z>Z { printf("ℤ"); }
<Z>\<= { printf("≤"); }
<Z>>= { printf("≥"); }
<Z>\< { printf("〈"); }
<Z>> { printf("〉"); }
<Z>\^ { printf("⁀"); }
<Z>\/\| { printf("↿"); }
<Z>\|\\ { printf("↾"); }
<Z>. { printf("%s", yytext); }

%%
int main() {
  yylex();
}
