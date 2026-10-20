# Canvis a `main.tex`: resolució dels comentaris en roig

Data: 2026-10-13. Fitxer: `sources/higher-order/main.tex`.

Hi havia set comentaris en roig (`\textcolor{red}{…}`); un vuité, «Subseccions
extra», ja l'havies esborrat tu abans de començar. Tots set s'han resolt i
eliminat. Totes les etiquetes LaTeX existents es conserven (el pla de
`sources/higher-order/*.toml` hi fa referència) i se n'han afegit de noves.
El document compila sense errors ni referències indefinides (pdflatex + bibtex).

Al final hi ha la llista de **decisions que has de revisar**.

---

## 1. Derivors generalitzats (`SGenDerivors`)

**Comentari.** No volem sorts ordenats ni predicats; treballem amb
E-equacions, no amb fórmules. La $d_{\mathbf{w},s}$ de l'apartat 3 ha de
correspondre amb la $d$ de la Definició `DDerivor`. Les paraules es denoten
$\mathbf{s}$. Un derivor generalitzat és una tripla $(\varphi, D, d)$ amb
$(\varphi,d)$ un derivor i $D$ un conjunt d'E-equacions per a cada sort.

**Què he fet.**

- He afegit un paràgraf de notació, que també fan servir les seccions 5 i 6:
  - $v^{\mathbf{t}}_{j}$ és la variable de $\downarrow\mathbf{t}$ corresponent a la lletra $j$.
  - $\mathrm{Eq}_{\Lambda}(X)=\coprod_{t}\mathrm{T}_{\Lambda}(X)^2_t$ és el conjunt de les E-equacions.
  - $\mathbf{B}\models\mathcal{E}[b]$ indica satisfacció sota una valoració; una família $\mathbf{b}\in B_{\mathbf{t}}$ s'identifica amb una valoració.
  - $f^{\sharp}[\mathcal{E}]$ és la substitució aplicada a un conjunt d'equacions.
- He reescrit `DGeneralDerivor`:
  - Un derivor generalitzat és $(\varphi,D,d)$, on $(\varphi,d)$ és un derivor en el sentit de `DDerivor` i $D_s\subseteq\mathrm{Eq}_\Lambda(\downarrow(\varphi(s)))$ són E-equacions en l'única variable $v^{\varphi(s)}_0$.
  - Defineix també $D_{\mathbf{s}}$ per a paraules: les condicions de cada lletra, reanomenades a la variable corresponent.
- He explicat la correspondència amb [LG18]: $D_s$ correspon a $\Delta_s(x)$, i $d_{\mathbf{s},s}(\sigma)$ correspon a $\Phi^\sigma$. Tot derivor és el derivor generalitzat $(\varphi,\varnothing,d)$.
- He afegit la nova Observació `RGenDerivorSem`, sobre la semàntica pretesa:
  - L'àlgebra $\mathbf{B}$ es restringeix als subconjunts $B^D_s$.
  - Perquè això done una $\Sigma$-àlgebra cal una **condició de clausura**. No l'he posada a la definició, perquè el comentari no la demanava. Apareix en forma sintàctica a la secció 6, com a condició (GEP1).

## 2. ep-derivors (`SEpDerivors`)

**Comentari.** Denotar una ep-signatura per $(S,\Sigma,\mathrm{def}^{\mathbf{\Sigma}})$.
Completar formalment $\mathrm{deft}^{\mathbf{\Sigma}}$ i l'operador de
conseqüència semàntica $\mathrm{Cn}$. Corregir la definició d'ep-derivor
tenint en compte el comentari que la seguia («I am not sure that this is the
correct definition…»).

**Què he fet** (la secció s'ha reescrit sencera):

- **`DEpSignature`** (nova): defineix l'ep-signatura $(S,\Sigma,\mathrm{def}^{\mathbf{\Sigma}})$ amb $\mathrm{def}^{\mathbf{\Sigma}}(\sigma)\subseteq\mathrm{Eq}_\Sigma(\downarrow\mathbf{s})$, el conjunt $A_{\mathrm{def}(\sigma)}$, les ep-àlgebres i la categoria $\mathsf{PAlg}(\mathbf{\Sigma})$. També corregeix les errades del text antic: $\mathbf{w}\to\mathbf{s}$ i «ordred». Una signatura total és el cas $\mathrm{def}=\varnothing$.
- **`RSubst`** (nova): lema de substitució per a àlgebres parcials. Només val quan els termes substituïts estan definits. Aquesta restricció és la causa de la correcció del punt 4 de més avall.
- **`DDeft`** (nova): $\mathrm{deft}^{\mathbf{\Sigma}}$ es defineix per recursió algebraica:
  $\mathrm{deft}(x)=\varnothing$ i
  $\mathrm{deft}(\sigma(P_j)_j)=\bigcup_j\mathrm{deft}(P_j)\cup(P_j)_j^{\sharp}[\mathrm{def}(\sigma)]$.
- **`LDeft`** (nou lema, amb prova): en una ep-àlgebra, $P^{\mathbf{A}}[a]$ està definit si i només si $\mathbf{A}\models\mathrm{deft}(P)[a]$. Aquesta és la justificació de $\mathrm{deft}$.
- **`DCn`** (nova): $\mathrm{Cn}^{\mathbf{\Sigma}}_X(\mathcal{E})$ és el conjunt de les E-equacions que valen en tota ep-àlgebra i sota tota valoració que satisfà $\mathcal{E}$. He afegit un paràgraf que diu que és un operador de clausura i que $\mathrm{Cn}(\mathcal{E})=\mathrm{Cn}(\mathcal{E}')$ si i només si $\mathcal{E}$ i $\mathcal{E}'$ tenen els mateixos models.
- **$\mathbf{d}^{\ast}(\mathbf{B})$**: la $\Sigma$-àlgebra parcial que s'obté interpretant cada $\sigma$ com l'operació terme parcial $d(\sigma)^{\mathbf{B}}$.
- **`DTranslation`** (nova) i **`LTranslation`** (nou lema, amb prova): la traducció $\mathrm{tr}_{\mathbf{d}}$ compleix que $\mathbf{d}^{\ast}(\mathbf{B})\models\mathcal{E}[\mathbf{b}]$ si i només si $\mathbf{B}\models\mathrm{tr}_{\mathbf{d}}[\mathcal{E}][\mathbf{b}]$. Vegeu el punt 4 de més avall.
- **`DDerivorEP`** (corregida). Abans era una còpia literal de `DDerivor`. Ara diu que un ep-derivor és un derivor tal que, per a cada $\sigma$,
  $$\mathrm{Cn}^{\mathbf{\Lambda}}(\mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])=\mathrm{Cn}^{\mathbf{\Lambda}}(\mathrm{deft}^{\mathbf{\Lambda}}(d_{\mathbf{s},s}(\sigma))).$$
- **`PEpDerivorFunctor`** (nova, amb prova): $\mathbf{d}$ és un ep-derivor **si i només si** $\mathbf{d}^{\ast}$ envia $\mathbf{\Lambda}$-àlgebres a $\mathbf{\Sigma}$-àlgebres. En aquest cas $\mathbf{d}^{\ast}$ és un functor $\mathsf{PAlg}(\mathbf{\Lambda})\to\mathsf{PAlg}(\mathbf{\Sigma})$.
- **`REpDerivor`** (nova): substitueix el paràgraf «I am not sure…» i explica les correccions.

**Les correccions a la definició antiga, i per què:**

1. **Inclusió → igualtat.** La inclusió
   $d^\sharp\times d^\sharp[\mathrm{def}(\sigma)]\subseteq\mathrm{Cn}(\mathrm{def}(d^\sharp(\sigma)))$
   només garanteix que el domini de $d(\sigma)^{\mathbf{B}}$ està contingut en el conjunt de les famílies que satisfan $\mathrm{def}(\sigma)$. L'operació podria quedar indefinida on hauria d'estar definida, i aleshores $\mathbf{d}^*(\mathbf{B})$ no seria una ep-àlgebra. La igualtat de conseqüències, que és la condició de Reichel, és **exactament** la que fa que $\mathbf{d}^*$ siga un functor; ho prova `PEpDerivorFunctor`. Això confirma la sospita del comentari.
2. **$\mathrm{def}(d^\sharp(\sigma))\to\mathrm{deft}^{\mathbf{\Lambda}}(d_{\mathbf{s},s}(\sigma))$.** $d(\sigma)$ és un terme, i cal $\mathrm{deft}$, no $\mathrm{def}$.
3. **$d^\sharp_{\mathbf{s},s}\to d^\sharp$ en totes les components.** Les equacions de $\mathrm{def}(\sigma)$ poden ser de qualsevol sort, no només de $s$.
4. **$d^\sharp\times d^\sharp\to\mathrm{tr}_{\mathbf{d}}$** (correcció nova, no demanada al comentari). Si $d(\sigma)$ no conté alguna variable, per exemple $d(\sigma)=v_0$ per a un $\sigma$ binari, aleshores $d^\sharp(\sigma(P_0,P_1))=d^\sharp(P_0)$ pot estar definit en $\mathbf{B}$ encara que $P_1$ no ho estiga en $\mathbf{d}^*(\mathbf{B})$. Per tant, $(d^\sharp P,d^\sharp Q)$ no expressa que $(P,Q)$ valga en $\mathbf{d}^*(\mathbf{B})$. $\mathrm{tr}_{\mathbf{d}}(P,Q)$ hi afegeix les equacions $(d^\sharp R,d^\sharp R)$ per a cada subterme $R$ de $P$ i de $Q$. Si cada $d(\sigma)$ conté totes les seues variables, aquestes equacions són redundants, i el text ho diu.

## 3. ep-derivors generalitzats (`SGenEpDerivors`)

**Comentari.** Completar una definició d'ep-derivor prenent com a base els
derivors generalitzats.

**Què he fet** (la secció era buida):

- **`DGenEpDerivor`** (nova): un ep-derivor generalitzat entre ep-signatures és un derivor generalitzat $(\varphi,D,d)$ tal que, per a cada $\sigma\in\Sigma_{\mathbf{s},s}$:
  - **(GEP1)**, preservació del domini:
    $d(\sigma)^{\sharp}[D_s]\subseteq\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{deft}^{\mathbf{\Lambda}}(d(\sigma)))$;
  - **(GEP2)**, condicions de domini dins dels dominis:
    $\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{tr}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])=\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{deft}^{\mathbf{\Lambda}}(d(\sigma)))$.

  $\mathbf{d}^*(\mathbf{B})$ té com a conjunt subjacent els $B^D_s$, i les operacions són les restriccions de $d(\sigma)^{\mathbf{B}}$.
- **`PGenEpDerivorFunctor`** (nova, amb prova): un ep-derivor generalitzat indueix un functor $\mathsf{PAlg}(\mathbf{\Lambda})\to\mathsf{PAlg}(\mathbf{\Sigma})$.
- **`RGenEpDerivor`** (nova): comprova la coherència amb les seccions anteriors:
  - els ep-derivors són el cas $D=\varnothing$;
  - per a signatures totals, (GEP2) és trivial i (GEP1) equival a la condició de clausura de `RGenDerivorSem`;
  - les dues condicions també són necessàries.

## 4. $\Sigma^{(n)}$ com a ep-signatura (`DSigmaCatCompact`)

**Comentari.** Completar $\Sigma^{(n)}$ com una ep-signatura on l'únic domini
de definició no trivial és
$\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_1),\mathrm{tg}^k_s(v^s_0))\}$.

**Què he fet.**

- A `DSigmaCatCompact` he afegit l'ep-signatura $\mathbf{\Sigma}^{(n)}=(S,\Sigma^{(n)},\mathrm{def}^{\mathbf{\Sigma}^{(n)}})$:
  - les condicions de domini són buides per a les operacions de $\Sigma$, per a $\mathrm{sc}^k_s$ i per a $\mathrm{tg}^k_s$;
  - per a la composició, $\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_0),\mathrm{tg}^k_s(v^s_1))\}$, on $v^s_0\circ^k_s v^s_1$ abreuja $\circ^k_s(v^s_0,v^s_1)$.
- **Observació `RCompactEp`** (nova): les ep-àlgebres de tipus $\mathbf{\Sigma}^{(n)}$ són exactament les $\Sigma^{(n)}$-àlgebres parcials que compleixen (A0), (A$^k$1) i (A$^k$3). Per tant, la QE-varietat de `DVarCompact` és la classe de les $\mathbf{\Sigma}^{(n)}$-àlgebres que compleixen la resta d'axiomes.

⚠️ **He invertit l'ordre de les variables respecte del comentari** (vegeu la decisió A).

## 5. Categoria compacta $\omega$ abans de `DSigmaCatCompact`, i cas $\omega$

**Comentari.** Escriure la definició de categoria compacta $\omega$ abans de
`DSigmaCatCompact`, i modificar `DSigmaCatCompact` perquè considere també el
cas $\omega$.

**Què he fet.**

- He mogut `DCompactOmegaCat` i `DOmegaCatAlg` just després de `DManySortedCatAlg`, amb una frase introductòria. He mogut també l'àlgebra, i no només la categoria, perquè és el seu anàleg natural.
- A `DSigmaCatCompact` ara $n\in\mathbb{N}\cup\{\omega\}$. La nota posterior diu que $\Sigma^{(n)}\subseteq\Sigma^{(m)}$ per a $n\le m\le\omega$ i que $\Sigma^{(\omega)}=\bigcup_n\Sigma^{(n)}$.
- Dins de `RCompactEp` he afegit una nota: **`DVarCompact` no s'estén a $n=\omega$.** La condició «tota cel·la és una $k$-cel·la per a algun $k$» no es preserva per productes, i les QE-varietats sí que són tancades per productes. El text en dona un contraexemple.

## 6. Notació $\circ^{(j,k)}$ a la presentació estesa

**Comentari.** La $j$-composició de $k$-cel·les es denotarà $\circ^{(j,k)}$,
com ja fan `DSigmaCatExtended` i `DVarExtended`.

**Què he fet.** He substituït $\circ^{(j)}$ i $\circ^{(i)}$ a `DOmegaCatExt`, a
les $n$-categories esteses i als $n$-functors estesos. L'índex superior és
sempre la dimensió de les cel·les compostes:

- **(MS3):** $\mathrm{sc}^{(j,k)}(g\circ^{(i,k)}f)=\mathrm{sc}^{(j,k)}(g)\circ^{(i,j)}\mathrm{sc}^{(j,k)}(f)$.
- **(MS8):** $\mathrm{i}^{(k,j)}(g\circ^{(i,j)}f)=\mathrm{i}^{(k,j)}(g)\circ^{(i,k)}\mathrm{i}^{(k,j)}(f)$. He eliminat la frase aclaridora («on the left … on the right …»), perquè la notació ja ho diu.
- **(MS9), (MS2), (MS6), (MS7):** $\circ^{(i,k)}$ i $\circ^{(j,k)}$, segons el cas.
- **Functors:** $F_k(g\circ^{(j,k)}f)=F_k(g)\circ'^{(j,k)}F_k(f)$.
- **Dades:** $\zeta_{j,k}=(\circ^{(j,k)},\mathrm{sc}^{(j,k)},\mathrm{tg}^{(j,k)},\mathrm{i}^{(k,j)})$. A més, «$j$-composition in $C_k$» ara diu «$j$-composition of $k$-cells».

Al document ja no hi queda cap $\circ^{(j)}$ ni cap $\circ^{(i)}$.

## 7. Moure `DOmegaExtCatAlg` i cas $\omega$ de `DSigmaCatExtended`

**Comentari.** Moure aquesta definició abans de `DSigmaCatExtended` i
modificar `DSigmaCatExtended` perquè considere també el cas $\omega$.

**Què he fet.**

- He mogut `DOmegaExtCatAlg` just després de `DExtCatAlg`, és a dir, abans de `DSigmaCatExtended`.
- A `DSigmaCatExtended` ara $n\in\mathbb{N}\cup\{\omega\}$. He introduït la notació $[n]$ per al conjunt de dimensions: $[n]=n+1$ si $n\in\mathbb{N}$, i $[\omega]=\omega$. Cal perquè, per a $\omega$, els sorts són $\omega\times S$ i no $(\omega+1)\times S$. He canviat $n+1$ per $[n]$ dins de la definició.
- La nota posterior diu que $\Sigma^{\mathrm{ext}(\omega)}$ és la unió de les imatges de les inclusions de $\Sigma^{\mathrm{ext}(n)}$, i que per a $n$ finit $[n]=n+1$, que és la notació de les altres definicions.

---

## Decisions que has de revisar

**A. Ordre dels arguments de $\circ^k_s$ (punt 4).** El comentari escrivia
$\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_1),\mathrm{tg}^k_s(v^s_0))\}$.
Amb la convenció del document, $x\circ^k_s y=\circ^k_s(x,y)$, i (A$^k$3) diu
que $x\circ^k_s y$ està definit si i només si
$\mathrm{sc}^k_s(x)=\mathrm{tg}^k_s(y)$. Amb $x=v^s_0$ i $y=v^s_1$, això dona
$(\mathrm{sc}^k_s(v^s_0),\mathrm{tg}^k_s(v^s_1))$, que és el que he escrit. La
versió del comentari correspon a l'ordre diagramàtic. Si la volies així, cal
canviar també (A$^k$3)–(A$^k$6) i (AB$^{l,k}$3). **Recomanació:** mantenir
l'ordre que he posat, que és coherent amb la resta del document.

**B. $\mathrm{tr}_{\mathbf{d}}$ en lloc de $d^\sharp\times d^\sharp$ (punt 2.4).**
És un canvi matemàtic que no demanava el comentari. Sense aquest canvi,
`PEpDerivorFunctor` és falsa per a derivors que «esborren» variables. Una
alternativa és restringir-se a derivors on cada $d(\sigma)$ conté totes les
seues variables i mantenir $d^\sharp\times d^\sharp$. **Recomanació:**
$\mathrm{tr}_{\mathbf{d}}$, que és més general i coincideix amb l'altra opció
en el cas regular.

**C. (GEP1) i (GEP2) són una proposta meua (punt 3).** Les he triat perquè
$\mathbf{d}^*$ siga un functor, i són també necessàries per a això. Si teniu en
ment una altra noció, per exemple sense (GEP1) o amb inclusió, caldrà ajustar
la definició.

**D. Les condicions de domini $D_s$ usen una única variable,** com $\Delta_s(x)$
a [LG18]. Si en algun moment cal que depenguen de més variables, caldria
canviar la definició.

**E. Cas $\omega$ de les especificacions.** No he estés `DVarCompact` a
$\omega$, perquè no és possible (vegeu el punt 5). En canvi, `DVarExtended`
**sí** que es podria estendre a $\omega$: en la presentació estesa no hi ha
condició de finitud, perquè cada cel·la viu en un sort $(k,s)$. No ho he fet
perquè el comentari no ho demanava. Ho proposo com a pas següent.

**F. Notació de variables.** L'Observació `Rdop` numera les variables de
$\downarrow\varphi^\star(\mathbf{s})$ per sorts, com a segments inicials. En
canvi, la secció de les àlgebres de Hall usa $v^{s_j}_j$, per posicions. Per
no prendre partit, he introduït $v^{\mathbf{t}}_j$, «la variable de la lletra
$j$». Caldria unificar les dues convencions algun dia.

**G. El pla de formalització.**
- Els ítems `DSigmaCatCompact` i `DSigmaCatExtended` de `compact.toml` i `extended.toml` estan marcats com a `done`. Ara les definicions inclouen el cas $\omega$, i la compacta també l'estructura d'ep-signatura, que el Lean actual (`compact.signature` i `extended.signature`) no cobreix. El propietari del pla (encosllo) hauria de decidir si cal revisar-los. No he tocat cap fitxer `.toml` ni cap fitxer Lean.
- Els trasllats de definicions no afecten el pla, perquè les referències són etiquetes i no números.
- Les seccions de derivors queden fora de l'abast actual del pla.

## Nous elements del document (etiquetes)

`RGenDerivorSem`, `DEpSignature`, `RSubst`, `DDeft`, `LDeft`, `DCn`,
`DTranslation`, `LTranslation`, `PEpDerivorFunctor`, `REpDerivor`,
`DGenEpDerivor`, `PGenEpDerivorFunctor`, `RGenEpDerivor`, `RCompactEp`.
`DGeneralDerivor` i `DDerivorEP` conserven l'etiqueta, però el contingut és nou.

---
---

# Segona ronda: nous comentaris en roig

Data: 2026-10-13. Hi havia 18 comentaris nous en roig, a més del bloc de
resultats sobre derivors que havies enganxat dins la secció d'ep-derivors
generalitzats. Tots s'han resolt i eliminat. El document compila sense
errors, sense referències indefinides i sense etiquetes duplicades (pdflatex +
bibtex). Ara té 113 pàgines.

Al final hi ha les **decisions que has de revisar**.

## 1. Estructura: comentar les seccions 3, 4 i 5

**Comentari.** Comentar les tres seccions anteriors (*Derivors*,
*Generalized derivors*, *ep-derivors*) i introduir directament els
*generalized ep-derivors*. La secció ha d'incloure les nocions anteriors que
calguen, excepte les àlgebres de Hall, que no s'han de copiar però de les quals
sí es poden fer servir els resultats.

**Què he fet.**
- He comentat les tres seccions línia a línia amb `%`; per recuperar-les, n'hi ha prou de llevar el `%`. Abans he esborrat els seus comentaris en roig, perquè els resol la secció nova.
- He reescrit la secció *Generalized ep-derivors*, que ara és la secció 3 del PDF, amb sis subseccions:
  1. **Notation**: variables, termes i subterme, E-equacions i substitucions. Dels derivors només recorde la definició i tres fets de l'apèndix, (H1)–(H3): $d^\sharp$ és un homomorfisme d'àlgebres de Hall i la composició és la de $\mathsf{Sig}_{\mathfrak d}$. No hi copie res de les àlgebres de Hall. Inclou `RSubst` i un remark nou, `RHomTerm`: els homomorfismes conserven els valors definits.
  2. **ep-signatures**: `DEpSignature`, `DDeft`, `LDeft` i `DCn`.
  3. **Generalized derivors and translations**: `DGeneralDerivor`, `PDeltaFunctor`, `DDerivedPAlg`, `DTranslation` i `LTranslation`.
  4. **Generalized ep-derivors**: `DGenEpDerivor`, `PGenEpDerivorAlg`, `PGenEpDerivorFunctor` i `RGenEpDerivor`.
  5. **La categoria $\mathsf{epSig}_{\mathfrak{gd}}$**: composició, `PEpSiggdCat`, `PGenAlgFun`, `PGenDerClCong` i `DEpAlgCat`.
  6. **Generalized ep-derivors between ep-specifications**: vegeu la decisió C.

## 2. Notació de variables (comentari a l'antiga §4)

**Comentari.** Prendre la notació de variables de la secció de *derived
operations* del document Curry-Howard.

**Què he fet.**
- He adoptat la notació $\downarrow\mathbf{s}$, amb $(\downarrow\mathbf{s})_s=\mathbf{s}^{-1}[\{s\}]$, i l'he identificada amb $V^S_{\mathbf{s}}=\{v^s_i\mid i\in|\mathbf{s}|_s\}$, numerades per sort com al Curry-Howard.
- Aquesta part del Curry-Howard ja és a l'apèndix del `main.tex`, així que hi faig referència (`DLR`, `isovsV`) i no cite el document, que ja no és a `Biblio.bib`.
- $v^{\mathbf{s}}_j$ queda només com a abreviatura de la variable corresponent a la lletra $j$. Així, $v^{\mathbf{s}}_j=v^{s_j}_i$ si aquella lletra és l'aparició $i$-èsima del seu sort.

## 3. Functor $\Delta_{(\varphi,D)}$ (comentari a l'antiga §4)

**Comentari.** Llevar el remark `RGenDerivorSem` i fer una proposició que
definisca $\Delta_{(\varphi,D)}$.

**Què he fet.**
- He eliminat el remark.
- He afegit la nova Proposició `PDeltaFunctor`. Defineix $\Delta_{(\varphi,D)}\colon\mathsf{PAlg}(\Lambda)\to\mathsf{Set}^S$, que envia $\mathbf{B}$ a $B_{(\varphi,D)}$ i $f$ a $f_\varphi|^{B_{(\varphi,D)}}_{A_{(\varphi,D)}}$, exactament com demanaves.
- Les fletxes són els homomorfismes, que conserven les E-equacions; per això el domini és $\mathsf{PAlg}(\Lambda)$.
- També demostre que $\Delta_{(\varphi,\varnothing)}=\Delta_\varphi\circ\mathrm{G}_\Lambda$.

## 4. Notació $\mathsf{epAlg}$

**Comentari.** $\mathsf{epAlg}(S,\Sigma,\mathrm{def}^{\mathbf\Sigma})$ ha de
ser la subcategoria plena de $\mathsf{PAlg}(S,\Sigma)$ de les ep-àlgebres, i
cal canviar la notació a tot el document.

**Què he fet.**
- L'he introduïda a `DEpSignature` i l'he usada a tot arreu on la categoria era d'ep-àlgebres.
- $\mathsf{PAlg}(\boldsymbol{\mathcal C}^{\dots})$ es manté per a les QE-varietats.
- Per a les categories compacta i estesa demostre la igualtat $\mathsf{PAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})=\mathsf{epAlg}(\mathbf{\Sigma}^{(n)},\mathcal{C}^{\mathbf{\Sigma}^{(n)}})$ (`RCompactEp`, `PExtendedIdent`), i el mateix per a l'estesa.

## 5. `RSubst`

**Comentari.** Llevar-lo si no s'usa a la resta del document.

**Què he fet.** Es fa servir a `LDeft`, `LTranslation`, `PDeltaFunctor` i
`PGenEpDerivorAlg`. Per tant, l'he mantingut, dins la subsecció de notació.

## 6. Equació de $\mathrm{Cn}$ més neta

**Què he fet.** He introduït la classe de models
$\mathrm{Mod}^{\mathbf\Sigma}_X(\mathcal E)$, de manera que la definició queda
$\mathrm{Cn}^{\mathbf\Sigma}_X(\mathcal E)=\{e\mid\mathrm{Mod}(\mathcal E)\subseteq\mathrm{Mod}(\{e\})\}$.

## 7. Termes i subterme del Curry-Howard

**Què he fet.**
- Uso $\mathrm{Subt}_\Sigma(P)$, el conjunt $S$-sortit de subterme, en lloc del meu $\mathrm{Sb}(P)$.
- També faig servir la seua caracterització recursiva.
- Totes dues són a l'apèndix; hi he afegit les etiquetes `DSubt` i `RSubt` perquè es puguen citar.

## 8. Els resultats sobre derivors, adaptats

**Comentari.** Adaptar `PFunSig`, `PDerClCong`, `PAlgFun`, el diagrama i
`DAlgCat` als *generalized ep-derivors*, mantenint-ne l'estil.

**Què he fet.**

| Original | Nova versió |
|---|---|
| `PFunSig` | `PGenEpDerivorFunctor`: $\mathrm{Alg}_{\mathfrak{gd}}(\mathbf d)=\mathbf d^\ast_{\mathfrak{gd}}$ |
| el diagrama | dins `PGenEpDerivorFunctor`: $\mathrm G_{\mathbf\Sigma}\circ\mathbf d^\ast_{\mathfrak{gd}}=\Delta_{(\varphi,D)}\circ\mathrm{In}$ |
| `PDerClCong` | `PGenDerClCong` |
| `PAlgFun` | `PGenAlgFun` |
| `DAlgCat` | `DEpAlgCat` ($\mathsf{epAlg}_{\mathfrak{gd}}$) |

- Les etiquetes són noves perquè les originals ja existien a l'apèndix; el bloc enganxat les duplicava.
- A `PGenDerClCong` no he pogut usar l'argument de l'original (el functor aplicat a la inclusió o a la projecció): el quocient d'una ep-àlgebra no és necessàriament una ep-àlgebra. Per això la prova és directa, per inducció sobre termes.

## 9. $\mathsf{epSig}_{\mathfrak{gd}}$, $\mathbf d^\ast_{\mathfrak{gd}}$ i el paràgraf convertit en proposició

**Què he fet.**
- El paràgraf que definia $\mathbf d^\ast(\mathbf B)$ és ara la Proposició `PGenEpDerivorAlg`, escrita amb $\Delta_{(\varphi,D)}$. És una equivalència: (GEP1)+(GEP2) es compleixen si i només si cada $\mathbf\Lambda$-àlgebra és tancada i $\mathbf d^\ast(\mathbf B)$ és una $\mathbf\Sigma$-àlgebra.
- `PGenEpDerivorFunctor` usa la notació $\mathbf d^\ast_{\mathfrak{gd}}$.
- La categoria és la Proposició `PEpSiggdCat`. **L'ordre és diferent del que demanaves**: vegeu la decisió B.

## 10. Graduació i unificació

**Què he fet.**
- **Graduació.** He definit el derivor $\mathbf g^{(n)}$ (`DGradDerivor`) a partir de la teua idea, amb dues correccions:
  - per a $n$ finit, $D_{(n,s)}=\varnothing$, perquè $\mathrm{sc}^n$ no existeix a $\Sigma^{(n)}$;
  - la identitat és $\mathrm i^{(k,j)}\mapsto v_0$, amb la notació $\mathrm i^{(k,j)}$ del document.
- `PGradDerivor` demostra (GEP1)–(GEP3): el functor transforma àlgebres compactes en esteses. La prova tradueix cada axioma (EA) a un axioma (A)/(AB).
- `DGraduation` defineix $\mathrm{Gd}^{(n)}_{\mathbf\Sigma}$ i la seua birestricció, també per a $n=\omega$.
- **Unificació.** He definit $\mathbf u^{(n)}$ (`DUnifDerivor`) a partir de la teua idea, amb $\#^k\mapsto\circ^{(k,n)}$. `PUnifDerivor` en demostra les propietats i `DUnification` defineix $\mathrm{Uf}^{(n)}$.
- **Unificació, cas $\omega$.** No pot venir d'un *generalized derivor* (vegeu la decisió E). L'he definida com un colímit dels casos finits (`DUnificationOmega`, `PUnificationOmega`).
- **Relació entre tots dos.**
  - `PUnifGrad`: $\mathrm{Uf}\circ\mathrm{Gd}=\mathrm{Id}$. Ho demostre veient que el derivor compost $\mathbf g\circ\mathbf u$ és equivalent a la identitat. Per a $\omega$, només és un isomorfisme natural.
  - `PGradUnif`: $\mathrm{Gd}\circ\mathrm{Uf}\cong\mathrm{Id}$, calculant el compost $\mathbf u\circ\mathbf g$.
  - Corol·lari nou `CGdUfEquiv`: totes dues són equivalències de categories.
- **Identificacions prèvies.** Per definir el functor sobre $\mathsf{nCatAlg}$, he afegit `PCompactIdent`, que demostra $\mathsf{nCatAlg}(\mathbf\Sigma)=\mathsf{PAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})$ i diu que, per a $\omega$, és una subcategoria plena pròpia. He afegit també `PExtendedIdent` per al cas estés.

## 11. Discretització i truncació

**Què he fet.**
- He reescrit la secció sencera; del text antic sobre la truncació no queda res.
- Per a $m\le n$, amb $n\in\mathbb N\cup\{\omega\}$, he definit els derivors de discretització, $\boldsymbol\delta^{(n,m)}$ i $\boldsymbol\delta^{\mathrm{ext}(n,m)}$, i de truncació, $\boldsymbol\tau^{(m,n)}$ i $\boldsymbol\tau^{\mathrm{ext}(m,n)}$. Demostre que són *generalized ep-derivors* (`PDiscDerivor`, `PDiscExtDerivor`, `PTruncExtDerivor`) i en definisc els functors $\mathrm D^{(n,m)}_{\mathbf\Sigma}$ i $T^{(m,n)}_{\mathbf\Sigma}$, en les versions compacta i estesa.
- **Relacions** (`PTruncDisc`, `PDiscTruncAdj`, `PTruncComp`):
  - $T\circ\mathrm D=\mathrm{Id}$, demostrat amb derivors compostos;
  - $\mathrm D\dashv T$, amb unitat identitat; la counitat és la inclusió de les $m$-cel·les en la versió compacta i $\mathrm i^{(k,m)}$ en l'estesa;
  - $T^{(m,n)}\circ T^{(n,p)}=T^{(m,p)}$, que és el fet que usen les seccions de límits. Ara el remark `RTmnCatAlgProjSys` hi remet.
- He conservat les etiquetes `DTmnCatAlg` i `DTmnExtCatAlg`, que són al pla. El functor és el mateix que abans: les $m$-cel·les són exactament les cel·les que són $k$-cel·les per a tot $k\ge m$, per (AB$^{m,k}$1).

## 12. Notació $[n]$

**Comentari.** No introduir $[n]$; usar $n+1$.

**Què he fet.**
- He reescrit `DSigmaCatExtended` per a $n\in\mathbb N$ amb $n+1$. Per a $\omega$ hi ha una frase final: «les mateixes clàusules amb $\omega$ en lloc de $n+1$».
- `DVarExtended` es completa de la mateixa manera per a $\omega$.
- `DVarCompact` admet ara $n\in\mathbb N\cup\{\omega\}$.

---

## Decisions que has de revisar (segona ronda)

**A. Condicions de domini per a cada operació, $D_\sigma$ (la decisió més important).**
- **Canvi.** Ara un *generalized derivor* $(\varphi,D,d)$ té $D=((D_s)_s,(D_\sigma)_\sigma)$: a més del domini de cada sort, hi ha un conjunt d'E-equacions que restringeix el domini de cada símbol.
- **Raó 1: discretització.** Sense $D_\sigma$, la discretització no pot venir de cap derivor. Cal que $x\circ^m y$ estiga definit si i només si $x=y$, i cap terme no ho expressa: en un monoide, vist com a categoria compacta, tot terme és total.
- **Raó 2: composició.** Sense $D_\sigma$, la composició de dos *generalized ep-derivors* no és en general un *generalized ep-derivor*. Si $\mathbf e$ oblida una variable, $(\mathbf e\circ\mathbf d)^\ast$ pot estar definit on $\mathbf d^\ast\circ\mathbf e^\ast$ no ho està.
- **Compatibilitat.** És la contrapartida de la fórmula $\Phi^\sigma$ de [LG18]. Amb $D_\sigma=\varnothing$ es recupera tot el que teníem: les teues idees per a $\mathrm{Gd}$ i $\mathrm{Uf}$ no en necessiten.

**B. Ordre de les proposicions.**
- **Què demanaves.** Primer la categoria $\mathsf{epSig}_{\mathfrak{gd}}$, després la proposició del paràgraf i després `PGenEpDerivorFunctor`.
- **Per què no ho he pogut fer.** La prova que el compost de dos *generalized ep-derivors* ho torna a ser necessita saber que $\mathbf e^\ast(\mathbf C)$ és una ep-àlgebra, que és justament la proposició del paràgraf.
- **Ordre que he fet servir.** `PGenEpDerivorAlg` → `PGenEpDerivorFunctor` → `PEpSiggdCat`. Ho explique en una frase al començament de la subsecció.

**C. Morfismes de $\mathsf{epSig}_{\mathfrak{gd}}$ com a classes d'equivalència.**
- **Problema.** La composició sintàctica (Definició `DGenEpComp`) no és associativa literalment, i la identitat no hi és neutra. Els conjunts d'equacions que resulten són diferents, encara que tinguen els mateixos models.
- **Solució.** Els morfismes són classes. Dos *generalized ep-derivors* són equivalents si tenen la mateixa $\varphi$ i el mateix functor.
- **Alternativa (no recomanada).** Normalitzar els conjunts $D$ a la seua clausura per $\mathrm{Cn}$; seria més feixuc d'escriure.

**D. Relativització a especificacions: ep-specifications i (GEP3).**
- **Problema.** El derivor de graduació no compleix (GEP1) sobre totes les $\mathbf\Sigma^{(n)}$-àlgebres: en una àlgebra on $\mathrm{sc}^j$ no és idempotent, la $j$-font d'una cel·la no és una $j$-cel·la. Per tant, «el functor entre ep-àlgebres» que demanaves no està definit sobre totes les ep-àlgebres, sinó només sobre els models de $\boldsymbol{\mathcal C}^{\mathbf\Sigma^{(n)}}$.
- **Solució.** He afegit la subsecció `SEpSpec`:
  - ep-especificacions $(\mathbf\Sigma,\mathcal E)$;
  - $\mathrm{Cn}^{\mathbf\Lambda,\mathcal F}$;
  - la condició (GEP3): $\mathbf d^\ast$ envia models a models;
  - un criteri sintàctic (`LTranslationQE`);
  - la Proposició `PGenEpSpec`, que estén tots els resultats a $\mathsf{epSpec}_{\mathfrak{gd}}$.
- **Relació amb el que demanaves.** $\mathsf{epSig}_{\mathfrak{gd}}$ és la subcategoria plena de les especificacions amb $\mathcal E=\varnothing$. La «birestricció» que demanaves és exactament (GEP3).

**E. La unificació $\omega$ no ve d'un derivor.**
- **Problema.** Un *generalized derivor* envia cada sort a un únic sort $(k,s)$, i per tant només veu cel·les d'una dimensió. L'argument és al text: una ω-categoria estesa amb una sola cel·la fins a la dimensió $k$.
- **Solució.** He definit $\mathrm{Uf}^{(\omega)}$ com el colímit de les àlgebres $\mathrm D^{(\omega,p)}\mathrm{Uf}^{(p)}T^{\mathrm{ext}(p,\omega)}(\mathbf A)$.
- **Conseqüència.** Per a $\omega$, els resultats de relació són isomorfismes naturals, no igualtats.

**F. Notació dels functors.**
- $T^{(m,n)}$ va en cursiva, com a les seccions de límits.
- La discretització és $\mathrm D^{(n,m)}$, com al Projecte-Investigador ($D^{(n+1,n)}_\Sigma$).
- La truncació tenia dues notacions: $U^{(n,n+1)}$ al Projecte-Investigador i $T^{(m,n)}$ al `main.tex`. He mantingut la del `main.tex`.

**G. Pla de formalització.**
- No he tocat cap `.toml` ni cap fitxer Lean.
- L'ítem `SDiscretization` de `truncation.toml` està «blocked» perquè la subsecció només tenia títol. Ara té contingut; el propietari del pla (encosllo) podria desbloquejar-lo.
- L'ítem `DTmnCatAlg, DTmnExtCatAlg` («done») defineix el mateix functor que abans, però ara també per a $n=\omega$ i a partir d'un derivor. Convé revisar-lo.
- Els ítems exclosos `SDerivors`, `SGenDerivors` i `SEpDerivors` apunten ara a seccions comentades.
- No he pogut executar `stemma check`, perquè Lean no està instal·lat en aquest entorn.

## Nous elements (segona ronda)

`SGenEpNotation`, `RHomTerm`, `SEpSignatures`, `SGenDerivorsTr`,
`PDeltaFunctor`, `DDerivedPAlg`, `RTrRegular`, `SGenEpDerivorsDef`,
`PGenEpDerivorAlg`, `SEpSiggd`, `DGenEpComp`, `LGenEpComp`, `PEpSiggdCat`,
`PGenAlgFun`, `PGenDerClCong`, `DEpAlgCat`, `SEpSpec`, `DEpSpec`,
`DGenEpDerivorSpec`, `LTranslationQE`, `PGenEpSpec`, `PCompactIdent`,
`PExtendedIdent`, `SGraduationSub`, `DGradDerivor`, `PGradDerivor`,
`DGraduation`, `SUnificationSub`, `DUnifDerivor`, `PUnifDerivor`,
`DUnification`, `DUnificationOmega`, `PUnificationOmega`, `SGradUnif`,
`CGdUfEquiv`, `DDiscDerivor`, `PDiscDerivor`, `DDiscretization`,
`DDiscExtDerivor`, `PDiscExtDerivor`, `DDiscretizationExt`, `DTruncDerivor`,
`PTruncExtDerivor`, `SDiscTrunc`, `PTruncDisc`, `PDiscTruncAdj`,
`PTruncComp`; i, a l'apèndix, `DLR`, `DSubt`, `RSubt`. Desapareixen `RGenDerivorSem` i les etiquetes que només eren a les seccions
comentades (`DDerivor`, `PSigdCat`, `DDerivorEP`, `PEpDerivorFunctor`,
`REpDerivor`, …). `DEpSignature`, `RSubst`, `DDeft`, `LDeft`, `DCn`,
`DTranslation`, `LTranslation`, `DGeneralDerivor`, `DGenEpDerivor`,
`PGenEpDerivorFunctor` i `RGenEpDerivor` es reutilitzen a la secció nova.

---
---

# Tercera ronda: respostes a les decisions A–E

Data: 2026-10-13. El document compila sense errors, sense referències
indefinides i sense etiquetes duplicades; ara té 118 pàgines.

## B. Notació $\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$

Totes les àlgebres transformades s'escriuen ara amb el subíndex:
$\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$,
$(\mathbf e\circ\mathbf d)^\ast_{\mathfrak{gd}}(\mathbf C)$,
$(\boldsymbol\delta^{(n,m)})^\ast_{\mathfrak{gd}}(\mathbf B)$, etc.
He fet 23 substitucions, totes a les seccions actives.

## E. Reestructuració del cas $\omega$

- **Seccions finites.** Les seccions de graduació/unificació
  (`SGraduation`) i de discretització/truncació (`STruncation`) ara només
  tracten casos finits ($n\in\mathbb N$, $m\le n$). Hi he afegit:
  - `PGdUfAdj`: $\mathrm{Gd}^{(n)}\dashv\mathrm{Uf}^{(n)}$, amb unitat la
    identitat i counitat $\theta^{-1}$. És una equivalència adjunta.
  - A `PTruncComp`, la igualtat $T^{(n,p)}\circ\mathrm D^{(p,m)}=\mathrm D^{(n,m)}$.
  - Nova subsecció `SCompatGdUf`, amb `PCompatGdUf`:
    1. $T^{\mathrm{ext}}\circ\mathrm{Gd}=\mathrm{Gd}\circ T$;
    2. $\mathrm{Gd}\circ\mathrm D=\mathrm D^{\mathrm{ext}}\circ\mathrm{Gd}$;
    3. $\mathrm{Uf}\circ\mathrm D^{\mathrm{ext}}=\mathrm D\circ\mathrm{Uf}$;
    4. $\mathrm{Uf}^{(m)}\circ T^{\mathrm{ext}(m,n)}\cong T^{(m,n)}\circ\mathrm{Uf}^{(n)}$,
       amb l'isomorfisme $\beta^{(m,n)}$ donat per les identitats $\mathrm i^{(n,m)}$.
- **`SLimitCompact`.**
  - Defineix les projeccions $T^{(n,\omega)}$ (`DTnOmegaCatAlg`).
  - Ara té la demostració de `PUnivPropCatAlg`, que no en tenia: el límit
    d'una família compatible és la unió de les cel·les, i cada operació es
    calcula en un nivell finit.
  - Afegeix el corol·lari `CLimitNat`: morfismes i transformacions naturals
    cap a $\omega\mathsf{CatAlg}$ es determinen nivell a nivell.
- **`SLimitExtended`.** Defineix $T^{\mathrm{ext}(n,\omega)}$
  (`DTnOmegaExtCatAlg`) i afegeix `CLimitNatExt`.
- **Nova secció `SOmegaFunctors`.** Els quatre functors $\omega$ es defineixen
  per la propietat universal:
  - **Truncació.** $T^{(m,\omega)}$ i $T^{\mathrm{ext}(m,\omega)}$ són les
    projeccions del límit.
  - **Graduació.** $\mathrm{Gd}^{(\omega)}$ es defineix per la família
    $\mathrm{Gd}^{(n)}\circ T^{(n,\omega)}$ (`DGdOmega`).
  - **Unificació.** La família $\mathrm{Uf}^{(n)}\circ T^{\mathrm{ext}(n,\omega)}$
    només és compatible llevat d'isomorfisme ($\beta$), i la propietat
    universal demana igualtats. Per això he introduït la *unificació
    normalitzada* $\widetilde{\mathrm{Uf}}^{(n)}$ (`LNormalForm`, `DNormUnif`,
    `LNormUnif`): cada cel·la es representa per la seua forma normal,
    $(k,y)$ amb $y$ una $k$-cel·la no degenerada. Aquesta família sí que és
    compatible estrictament, i defineix $\mathrm{Uf}^{(\omega)}$ (`DUfOmega`).
    També explique per què no pot venir d'un derivor (el contraexemple del
    monoide $\{e,f\}$).
  - **Discretització.** $\mathrm D^{(\omega,m)}$ i $\mathrm D^{\mathrm{ext}(\omega,m)}$
    es defineixen per les famílies $F_n$ (discretització si $n\ge m$,
    truncació si $n\le m$) (`DDiscOmega`).
  - **Relacions.**
    - `POmegaGdUf`: $\mathrm{Uf}^{(\omega)}\mathrm{Gd}^{(\omega)}\cong\mathrm{Id}$ i
      $\mathrm{Gd}^{(\omega)}\mathrm{Uf}^{(\omega)}\cong\mathrm{Id}$; hi ha una
      equivalència adjunta.
    - `POmegaDiscTrunc`: $T\circ\mathrm D=\mathrm{Id}$ i $\mathrm D\dashv T$, en
      les versions compacta i estesa.
- **Quadrat algebraic (`SAlgSquare`).**
  - **Nivell $(n,m)$** (`PAlgSquareFinite`, amb diagrama):
    - $\mathsf C=\mathsf{mCatAlg}$, $\mathsf D=\mathsf{mCat^{ext}Alg}$,
      $\mathsf C'=\mathsf{nCatAlg}$, $\mathsf D'=\mathsf{nCat^{ext}Alg}$;
    - horitzontals $\mathrm{Gd}\dashv\mathrm{Uf}$; verticals $\mathrm D\dashv T$;
    - $\alpha=\mathrm{id}$ (igualtat estricta) i $\beta=\beta^{(m,n)}$.
  - **Nivell $(\omega,m)$** (`PAlgSquareOmega`):
    - el mateix amb $\mathsf C'=\omega\mathsf{CatAlg}$ i $\mathsf D'=\omega\mathsf{Cat^{ext}Alg}$;
    - $\alpha=\mathrm{id}$, per la unicitat de la propietat universal;
    - $\beta=\nu^{-1}$: cada $m$-cel·la va a la seua forma normal.
- **Correcció a `DefAlgSquare`.** El text deia «adjunction from
  $\mathsf D$ to $\mathsf C$», etc. Amb la convenció de `DAdj`, això fa que
  $F\colon\mathsf D\to\mathsf C$, i aleshores $F'\circ J$ i $H\circ F$ no
  tipen. El diagrama, en canvi, posa $F\colon\mathsf C\to\mathsf D$, que sí
  que tipa. He reescrit els quatre ítems indicant explícitament els tipus i
  quin és l'adjunt esquerre, d'acord amb el diagrama. El document
  Curry-Howard (Definició 2.1.8) té la mateixa ambigüitat.

## A, C i D

Les he resolt en la ronda següent; vegeu més avall.

---
---

# Quarta ronda: nou disseny dels *generalized ep-derivors* (A, C, D)

Data: 2026-10-13. Has acceptat A i C. Per a D has triat definir el functor
sobre totes les àlgebres parcials i comprovar després que envia models a
models. He reescrit la secció *Generalized ep-derivors* i les proves que en
depenen. El document compila sense errors i sense referències indefinides ni
etiquetes duplicades.

## A. Sense $D_\sigma$

- **Generalized derivor.** Torna a ser $(\varphi,D,d)$, amb un domini per
  a cada sort (`DGeneralDerivor`).
- **El domini d'una operació no és una dada.** Es defineix per recursió:
  - $\mathrm{Dom}_{\mathbf d}(\sigma)$ =
    $D_{\mathbf s}\cup\mathrm{tr}_{\mathbf d}[\mathrm{def}(\sigma)]\cup\{(d\sigma,d\sigma)\}\cup d(\sigma)^\sharp[D_s]$;
  - és a dir: els arguments són als dominis, les condicions de domini de
    $\sigma$ traduïdes es compleixen, $d(\sigma)$ està definit i el seu
    valor cau dins del domini (`DDomTr`);
  - la traducció $\mathrm{tr}_{\mathbf d}$ i les condicions de definició
    $\mathrm{dfd}_{\mathbf d}$ dels subterme es defineixen alhora.
- **Hipòtesi nova.** Perquè la recursió estiga ben fundada, les
  ep-signatures han de complir que la relació «$\tau$ apareix a
  $\mathrm{def}(\sigma)$» siga ben fundada. Ho he afegit a `DEpSignature`, i
  ho he comprovat per a $\mathbf\Sigma^{(n)}$ i $\mathbf\Sigma^{\mathrm{ext}(n)}$.
- **Discretització.** Ja no necessita cap dada extra: la condició de domini
  de $\circ^k$ es tradueix a $v_0=v_1$.

## C. Categoria estricta, sense quocients

- **Dominis tancats.** Els dominis $D_s$ d'un *generalized ep-derivor* han
  de ser tancats per $\mathrm{Cn}$ respecte de l'especificació de destinació.
  Als exemples, els escrivim pels generadors.
- **Composició.** El domini compost és
  $\mathrm{Cn}(E\cup\mathrm{tr}_{\mathbf e}[D_s])$.
- **Resultat.** $\mathsf{epSpec}_{\mathfrak{gd}}$ és una categoria estricta
  (`PEpSiggdCat`), i $\mathsf{epSig}_{\mathfrak{gd}}$ n'és la subcategoria
  plena de les ep-signatures.
- **Conseqüència.** Les igualtats entre derivors compostos són ara igualtats
  de veritat, no equivalències: $\mathbf g\circ\mathbf u=\mathrm{id}$,
  $\boldsymbol\delta\circ\boldsymbol\tau=\mathrm{id}$, i les composicions
  de truncacions i de discretitzacions.

## D. Functor sobre totes les àlgebres parcials

- **Functor.** Per a qualsevol *generalized derivor*,
  $\mathbf d^\ast_{\mathfrak{gd}}$ és un functor
  $\mathsf{PAlg}(\Lambda)\to\mathsf{PAlg}(\Sigma)$, sense cap condició
  (`DDerivedPAlg`, `PGenEpDerivorFunctor`).
- **Definició.** Un *generalized ep-derivor* entre ep-especificacions és un
  *generalized derivor*, amb els dominis tancats, que envia models a models
  (`DGenEpDerivor`).
- **Criteri sintàctic** (`PGenEpDerivorAlg`):
  - (GEP1): les condicions de domini traduïdes impliquen que $d(\sigma)$
    està definit i cau dins del domini;
  - (GEP2): es compleixen els axiomes.
- **Composició.** Només funciona sobre els models (`LGenEpComp`), com havies
  acceptat. Al text hi ha un comentari que ho explica.
- **Les sis construccions** ($\mathrm{Gd}$, $\mathrm{Uf}$, $\mathrm D$,
  $T$, compactes i esteses) es defineixen ara sobre totes les àlgebres
  parcials. Les proposicions corresponents en comproven les dues condicions
  i en prenen la birestricció a les àlgebres categorials.

## Altres canvis

- **Eliminats.** `DDeft` i `LDeft` (la $\mathrm{deft}$ de Reichel), que ja
  no es feien servir; també la subsecció `SEpSpec` i els resultats
  `PGenEpSpec`, `LTranslationQE` i `RTrRegular`, que ara són innecessaris.
- **Nous.** `DDomTr`, `PDomainDef` (el domini de $\sigma$ en
  $\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$ és on es compleixen les seues
  condicions de domini i $d(\sigma)$ està definit i cau dins del domini), i
  un comentari després de `LGenEpComp`: dos *generalized ep-derivors* amb les
  mateixes $\varphi$ i $d$ són iguals si tenen els mateixos dominis als models.
- **Diferència amb Reichel.** El `RGenEpDerivor` ara la indica: Reichel exigeix
  que les condicions traduïdes siguen *equivalents* a la definició de
  $d(\sigma)$; ací només es demana una implicació, perquè el domini de
  $\sigma$ queda retallat per les condicions de domini.

---
---

# Cinquena ronda: introducció directa dels *generalized ep-derivors*

Data: 2026-10-13.

**Comentari.** La secció no ha de passar per «generalized derivor» ni per
«ep-derivor»: ha d'introduir directament la noció de *generalized
ep-derivor*, tan simplificada com siga possible i autocontinguda.

**Què he fet.**
- **Nova definició `DGenEpDerivor`.** És l'única definició de la noció i ara
  obri la subsecció. Un *generalized ep-derivor* entre ep-especificacions és
  una tripla $(\varphi,D,d)$ que compleix quatre condicions:
  1. $\varphi$ és una aplicació entre els conjunts de sorts;
  2. per a cada sort, un domini $D_s$ tancat;
  3. per a cada símbol, un terme $d(\sigma)$, és a dir, $(\varphi,d)$ és un
     derivor;
  4. per a cada model $\mathbf B$, $\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$
     és un model.
- **Ordre de la resta de la subsecció.** Defineix $\mathbf d^\ast_{\mathfrak{gd}}$
  per a qualsevol tripla que complisca (1)–(3) i sobre qualsevol àlgebra
  parcial. Els resultats van en aquest ordre:
  - $\Delta_{(\varphi,D)}$;
  - el domini i la traducció;
  - $\mathbf d^\ast_{\mathfrak{gd}}(\mathbf B)$;
  - el lema de traducció;
  - la caracterització del domini;
  - el functor;
  - els subconjunts tancats i les congruències;
  - el criteri sintàctic (GEP1)–(GEP2) per a la condició (4);
  - el remark.
- **Eliminat.** La definició `DGeneralDerivor` i l'expressió «generalized
  derivor» han desaparegut de tot el document actiu. Les construccions de les
  seccions posteriors es diuen ara «el triple … definit com segueix», i les
  proposicions corresponents en demostren que és un *generalized ep-derivor*.
- **Introducció.** La de la secció parla directament de *generalized
  ep-derivors*.
- **Subsecció fusionada.** L'antiga subsecció *Generalized derivors and their
  functors* desapareix: el seu contingut s'ha integrat a *Generalized
  ep-derivors*.

---
---

# Sisena ronda: apèndix comentat

Data: 2026-10-13.

**Comentari.** Comentar tota la informació de l'apèndix excepte la
bibliografia.

**Què he fet.**
- **Apèndix comentat.** Totes les línies, des de `\appendix` fins just abans
  de `\bibliographystyle`, estan comentades amb `%`. La bibliografia continua
  activa. El PDF passa de 117 a 47 pàgines.
- **Referències que s'haurien trencat.** El text principal en tenia 15 cap a
  l'apèndix. Per mantindre'l autocontingut:
  - **Notació** (subsecció `SGenEpNotation`).
    - Les variables $\downarrow\mathbf s$ es defineixen directament, sense
      els functors $L$, $R$ ni $\vartheta$.
    - $\mathrm{Subt}_\Sigma(P)$ es defineix per recursió.
    - Els derivors es defineixen directament: $d^\sharp$ per recursió sobre
      termes, amb (H1)–(H2) com a definició i (H3) com a conseqüència. Ja no
      es parla d'àlgebres de Hall.
  - **Preliminars.** Nova subsecció `SAdjGrot` amb les definicions
    d'adjunció (`DAdj`) i de construcció de Grothendieck (`DGConst`). Les
    etiquetes són les mateixes, de manera que les referències continuen
    funcionant.
  - **Altres referències.**
    - Subconjunts tancats i congruències: definits en la frase que precedeix
      `PGenDerClCong`.
    - $\mathsf{PAlg}(\Sigma)$: remet a `DPartialAlg`.
    - Els functors de derivors ordinaris: remeten a [CVST10b].
    - Monoide lliure: he llevat la referència a l'apèndix.
- **Resultat.** El document compila sense errors i sense referències
  indefinides.

---
---

# Setena ronda: *generalized ep-derivors* entre ep-signatures

Data: 2026-10-13.

**Comentari.** Els derivors no han d'estar definits sobre ep-especificacions,
sinó sobre ep-signatures. Després cal demostrar, quan calga, que els functors
corresponents envien models d'una especificació a models de l'altra.

**Què he fet.**
- **`DGenEpDerivor`.** Un *generalized ep-derivor* de $\mathbf\Sigma$ a
  $\mathbf\Lambda$ (ep-signatures) és ara simplement una tripla
  $(\varphi,D,d)$: una aplicació entre sorts, un domini $D_s$ per a cada sort
  i un terme $d(\sigma)$ per a cada símbol. Desapareixen les condicions de
  tancament i de models.
- **Functor.** $\mathbf d^\ast_{\mathfrak{gd}}$ és un functor entre totes les
  àlgebres parcials, sense cap condició.
- **Nova subsecció `SEpModels`.**
  - **Propietat.** «$\mathbf d^\ast_{\mathfrak{gd}}$ envia models de
    $(\mathbf\Lambda,\mathcal F)$ a models de $(\mathbf\Sigma,\mathcal E)$» és
    una propietat del derivor (`DSendsModels`).
  - **Criteri sintàctic.** És (GEP1)–(GEP2) (`PGenEpDerivorAlg`).
  - **Ep-especificacions.** Només s'usen per descriure classes de models.
- **Composició** (`DGenEpComp`, `LGenEpComp`).
  - **Definició.** Està definida per a qualssevol *generalized ep-derivors*
    entre ep-signatures.
  - **Lema.** Si $\mathbf e^\ast$ envia models a models i $\mathbf d^\ast$
    també, el compost també ho fa, i coincideix amb $\mathbf d^\ast\circ\mathbf e^\ast$
    sobre els models.
- **Nou remark `RSameFunctor`.** Dos derivors amb les mateixes $\varphi$ i
  $d$, i dominis amb els mateixos models en una classe d'àlgebres, indueixen
  el mateix functor en aquesta classe.
- **Categoria $\mathsf{epSig}_{\mathfrak{gd}}$** (`PEpSiggdCat`).
  - **Objectes:** les ep-signatures.
  - **Morfismes:** els *generalized ep-derivors* tancats que envien àlgebres
    a àlgebres.
  - **Per què aquestes condicions:** sense elles la composició no seria
    associativa ni la identitat neutra.
  - **Conseqüència:** els derivors de graduació, unificació, discretització
    i truncació no en són morfismes, perquè només envien models a models.
    El text ho explica.
- **Construccions de les seccions 6 i 7.**
  - Es defineixen ara com a *generalized ep-derivors* entre les ep-signatures
    $\mathbf\Sigma^{(n)}$ i $\mathbf\Sigma^{\mathrm{ext}(n)}$, amb dominis
    escrits directament: per exemple,
    $D_{(k,s)}=\{(v_0,\mathrm{sc}^k v_0)\}$.
  - Cada proposició demostra que el functor corresponent envia els models
    dels axiomes a models.
  - Hi ha igualtats exactes: $\mathbf g\circ\mathbf u=\mathrm{id}$ i
    $\boldsymbol\delta\circ\boldsymbol\tau=\mathrm{id}$.
  - La composició de truncacions es demostra amb `RSameFunctor`.
- **Eliminat.** La categoria $\mathsf{epSpec}_{\mathfrak{gd}}$.
- **Resultat.** El document compila sense errors i sense referències
  indefinides.

---

# Canvis a `scratch/share/higher-order/main.tex`: segona ronda de comentaris en roig

Data: 2026-10-15. Fitxer: `scratch/share/higher-order/main.tex`.

Hi havia 27 comentaris en roig. Tots s'han resolt i eliminat; l'eliminació
de les línies comentades l'has executada tu (vegeu l'apartat 21). El document compila sense errors ni referències indefinides
(pdflatex + bibtex). Commits: `4f39b94`, `9422ccc`, `6c2deef`, `b93ccbb`,
`f421c97`.

Les teues respostes a les preguntes inicials:

- Functor $\mathbf{d}^{\ast}_{\mathfrak{gd}}$: **es manté definit sobre
  $\mathsf{PAlg}$**, i a partir d'ací es treballa en $\mathsf{EPAlg}$.
- $\mathsf{hepAlg}_{\mathfrak{gd}}$: **reescrit via Grothendieck**, amb una
  categoria intermèdia d'ep-àlgebres febles.
- Aquest registre: **secció nova al final**, sense tocar el que ja hi havia.
- Dimensió finita en $\omega$: **remarca amb la prova** que no és expressable.

Al final hi ha la llista de **decisions que has de revisar** i la de les
**equacions massa llargues**.

---

## 1. Introducció i prerequisits (`SIntroduction`)

**Comentaris.** «Neteja tota aquesta subsecció. Fes que siga llegible.»
«Escriu una introducció per a l'article», amb l'estil de Curry-Howard o del
projecte investigador.

**Què he fet.**

- **Introducció nova**, amb l'estructura de la del document Curry-Howard:
  - Tres paràgrafs de motivació: què són les àlgebres categorials d'ordre
    superior; les presentacions single-set i globular; la idea dels
    derivors hep generalitzats, a partir de [CVST10b] i [LG18].
  - Una subsecció «Our work» que resumeix secció per secció el que es fa,
    amb referències a les seccions.
- **Prerequisits** reescrits en paràgrafs curts amb títol: *Set theory*,
  *Ordinals*, *Functions and mappings*, *Subsets and images*, *Categories*.
  - He eliminat les línies comentades de dins i les nocions que el text no
    usa (refinaments de relacions, $0_{A,B}$, parells de Kuratowski).
  - He simplificat la fórmula del domini del compost de dues aplicacions
    parcials: ara és $\mathrm{Dom}(g\circ f)=f^{-1}[\mathrm{Dom}(g)]$, que
    és equivalent a l'anterior.
  - $\mathsf{Cat}$ es defineix com la categoria de les
    $\mathcal{U}$-categories. He tret la citació a `GW23`, perquè no és a
    `Biblio.bib`.

## 2. Abstract

**Comentari.** «Escriu un abstract per a l'article.»

**Què he fet.** Un abstract (entorn `abstract` d'amsart, abans de
`\maketitle`) que resumeix els dos blocs del treball: els derivors hep
generalitzats amb la construcció de Grothendieck, i l'aplicació a les
àlgebres categorials (presentacions, functors, límits projectius i quadrats
algebraics).

## 3. Preliminars (`SPreliminaries`)

**Comentaris.** Reescriure tota la secció copiant les definicions del
document Curry-Howard tal qual, sense simplificar-les, perquè la secció siga
tan completa com siga possible. Substituir «Variables» i «Substitutions» pel
que diu Curry-Howard.

**Què he fet.** He reescrit la secció a partir de l'apèndix de Curry-Howard,
amb les definicions copiades sense simplificar. Subseccions, en aquest
ordre:

1. **Many-sorted sets** (`SManySortedSets`): conjunts i aplicacions
   $S$-sortals, $\Delta_\varphi$, productes, la propietat universal, les
   parts, la birestricció.
2. **Free monoids** (`SFreeMonoids`): paraules, longitud, subparaules,
   ocurrències.
3. **Many-sorted algebras** (`SManySortedAlg`): signatures, àlgebres,
   subàlgebres, $\mathrm{Sg}$, principi de prova per inducció algebraica.
4. **The free algebra** (`SFreeAlg`): files, l'àlgebra lliure, la
   caracterització dels termes, la propietat universal i l'adjunció.
5. **Variables and substitutions** (`SVariables`): substitueix les dues
   parts antigues; és la de Curry-Howard.
6. **Derivors** (`SPrelimDerivors`): àlgebres de Hall, derivors, la
   categoria $\mathsf{Sig}_{\mathfrak{d}}$.
7. **Many-sorted partial algebras** (`SPartialAlg`): àlgebres parcials,
   isomorfismes, productes.
8. **Terms and equations** (`STermsEq`): operacions terme, E-equacions,
   QE-equacions, satisfacció.
9. **Adjunctions, corestrictions and the Grothendieck construction**
   (`SAdjunctions`): adjuncions; restricció i correstricció d'un functor
   (vegeu l'apartat 7); construcció de Grothendieck per a categories
   indexades escindides i per a **categories indexades laxes normals**
   (nova, `DLaxIndexed`, `DLaxGConst`, `PLaxGConst`, amb la prova que és una
   categoria).

## 4. Sense assumpcions generals

**Comentaris.** «No faces la següent assumpció. Sempre que necessites
qualsevol d'aquestes coses nombra-les.» El mateix per a les hep-signatures:
«Aquest comentari aplica a tot el document.»

**Què he fet.** He eliminat totes les assumpcions generals («Throughout this
section…»). Ara cada definició, lema i proposició diu explícitament les
dades que usa. Per exemple: «Let $\mathbf\Sigma=(S,\Sigma,\mathrm{def}^{(S,\Sigma)})$
and $\mathbf\Lambda=(T,\Lambda,\mathrm{def}^{(T,\Lambda)})$ be
hep-signatures, $\mathbf d=(\varphi,d,\mathrm{Dom}^{(\varphi,d)})$ a
generalized hep-derivor…». Això s'aplica a tot el document, també a les
seccions 4–10.

## 5. Proposició `PTransformedAlg`

**Comentari.** Eliminar de l'enunciat la construcció («and in which, for
every…») i dur-la a la demostració, amb l'enunciat curt que proposaves.

**Què he fet.** L'enunciat és ara el curt. Tota la construcció
(recursió bé fundada sobre la jerarquia de la signatura) és a la
demostració.

**A revisar.** L'enunciat que proposaves deia «there exists a **unique**
partial $\Sigma$-algebra … whose underlying set is $B_{\mathrm{Dom}}$». Així
no és cert: sobre un mateix conjunt hi ha moltes àlgebres parcials. He tret
«unique». Si vols unicitat, l'enunciat ha de dir també com actuen les
operacions.

## 6. $\mathsf{EPAlg}$ en lloc de $\mathsf{PAlg}$

**Comentaris** (tres, aplicables a tot el document). No parlar de
$\mathsf{PAlg}$ sempre que es puga treballar en $\mathsf{EPAlg}$.

**Què he fet.**

- El functor $\mathbf d^\ast_{\mathfrak{gd}}$ continua definit de
  $\mathsf{PAlg}(\Lambda)$ en $\mathsf{PAlg}(\Sigma)$ (la teua resposta):
  - El transformat d'una ep-àlgebra no sempre és una ep-àlgebra; ho
    caracteritza `PTransformedEpAlg`.
  - El compost només es compara bé fora de les ep-àlgebres.
- A les seccions 4–10, totes les categories són $\mathsf{EPAlg}(\cdot,\cdot)$
  de les especificacions corresponents. Cada functor es construeix així:
  1. Es restringeix $\mathbf d^\ast_{\mathfrak{gd}}$ a la ep-varietat.
  2. Es demostra, amb `PTransformedEpAlg`, que el transformat és una
     ep-àlgebra.
  3. Es comprova que satisfà els axiomes.
- Han desaparegut els resultats que només servien per passar de
  $\mathsf{PAlg}$ a $\mathsf{EPAlg}$: `CSingleSetEp`, `CGlobularEp`,
  `PSingleSetIdentObj/Hom/Omega` i `PGlobularIdentObj/Hom`.

## 7. Correstricció com a noció preliminar

**Comentari.** No introduir la correstricció com una noció nova; si de cas,
als preliminars.

**Què he fet.** La restricció i la correstricció d'un functor a
subcategories plenes són ara la Definició `DCorestriction` dels
preliminars, en general. La subsecció «Restriction to ep-varieties»
(`SEpRestriction`) només l'aplica.

## 8. Eliminada `PGenHepDerivorAlg`

**Comentari.** No introduir-la; per veure que un functor correstringeix a
una varietat, referenciar `PTransformedEpAlg` i demostrar els axiomes.

**Què he fet.** L'he eliminada. Cada prova de correstricció (graduació,
unificació, discretització, truncació, i les versions en $\omega$) segueix
ara aquest esquema: `PTransformedEpAlg` + comprovació dels axiomes de la
varietat.

## 9. $\mathsf{hepAlg}_{\mathfrak{gd}}$ via Grothendieck

**Comentari.** Si es podria obtenir $\mathsf{hepAlg}_{\mathfrak{gd}}$ amb un
pseudofunctor o una construcció de Grothendieck.

**Resposta.** Sí, però amb un functor **lax normal**, no amb un
pseudofunctor:

- En general, $\mathbf d^\ast_{\mathfrak{gd}}\circ\mathbf e^\ast_{\mathfrak{gd}}$
  només està **contingut** en $(\mathbf e\circ\mathbf d)^\ast_{\mathfrak{gd}}$,
  no és igual ni isomorf.
- A més, $\mathbf d^\ast_{\mathfrak{gd}}$ no envia ep-àlgebres a
  ep-àlgebres.

**Què he fet.**

- **Ep-àlgebres febles** (`DWeakEpAlgebra`): àlgebres parcials amb
  $\mathrm{Dom}(\sigma^{\mathbf A})\subseteq A_{\mathrm{def}(\sigma)}$.
  Formen la categoria $\mathsf{wEPAlg}(\mathbf\Sigma)$. Sobre elles:
  - El derivor identitat actua com la identitat.
  - Els transformats continuen sent febles (`LHepWeak`).
- Les inclusions $\kappa^{\mathbf d,\mathbf e}$ fan de $(\mathrm{wEPAlg},\kappa)$
  una **categoria indexada laxa normal** sobre $\mathsf{hepSig}_{\mathfrak{gd}}$
  (`PHepLax`). La coherència és immediata perquè totes les $\kappa$ són
  inclusions.
- $\mathsf{hepAlg}_{\mathfrak{gd}}$ (`DHepAlgCat`) és la subcategoria plena
  de la construcció de Grothendieck formada pels parells
  $(\mathbf\Sigma,\mathbf A)$ amb $\mathbf A$ una ep-àlgebra.
- La remarca `RHepAlgCat` explica que es recupera $\mathsf{Alg}_{\mathfrak d}$
  de [CVST10b].

## 10. Composició $\circ$ en lloc de $\#$

**Comentari.** Des d'aquell punt fins al final de la secció, la composició
de les categories single-set es denota $\circ$.

**Què he fet.** He substituït $\#$ per $\circ$ a tota la secció single-set.

## 11. $\mathsf{nCatAlg}=\mathsf{EPAlg}$ com a remarca

**Comentari.** Presentar la igualtat com una remarca, com al projecte
investigador.

**Què he fet.**

- Remarques `RSingleSetIdent` i `RSingleSetIdentOmega` (single-set) i
  `RGlobularIdent` (globular). Diuen que, amb la identificació evident,
  $\mathsf{nCatAlg}(\mathbf\Sigma)=\mathsf{EPAlg}(\mathbf\Sigma^{(n)},\mathcal C^{\mathbf\Sigma^{(n)}})$,
  i igualment en el cas globular.
- La prova que són ep-varietats és a `PSingleSetEp` i `PGlobularEp`.

## 12. Dimensió finita en $\omega$

**Comentari.** Si la condició que cada cel·la té dimensió finita es podria
expressar amb algun axioma, per unificar la presentació de les
$\omega$-categories amb la de les $n$-categories.

**Resposta.** No es pot amb QE-equacions. Proposició nova
`PFiniteDimNotQE`:

- Les classes definides per QE-equacions són tancades per productes.
- El producte de les $n$-categories discretitzades, per a tots els $n$,
  té una cel·la de dimensió infinita.
- Per tant, $\omega\mathsf{CatAlg}(\mathbf\Sigma)$ és una subcategoria plena
  pròpia de la ep-varietat.

En la presentació globular el problema no apareix, perquè cada dimensió és
un sort. Així, $\omega\mathsf{Cat}^{\mathrm{gl}}\mathsf{Alg}$ sí que és una
ep-varietat.

## 13. Notació dels derivors

**Comentari.** Escriure
$\mathbf{Gd}^{(n)}_{\mathbf\Sigma}=(\varphi^{\mathrm{Gd}^{(n)}_{\mathbf\Sigma}},\mathrm{Gd}^{(n)}_{\mathbf\Sigma},\mathrm{Dom}^{\mathrm{Gd}^{(n)}_{\mathbf\Sigma}})$,
amb `\mathrm`; s'aplica als quatre derivors.

**Què he fet.** He canviat la notació dels quatre derivors
($\mathbf{Gd}$, $\mathbf{Uf}$, $\mathbf{Ds}$, $\mathbf{Tr}$), en les
versions single-set i globular i en $\omega$, i a totes les referències.

## 14. Sense abreviatures del tipus $\mathbf A=\mathrm{Gd}(\mathbf B)$

**Comentaris** (dos, aplicables a tot el document). Escriure sempre
l'expressió sencera, encara que les equacions s'allarguen.

**Què he fet.** He eliminat totes les abreviatures d'aquest tipus. Les
equacions que han quedat massa llargues són a la llista del final.

## 15. Notació de les transformacions naturals

**Comentari.** Escriure
$\theta=(\theta_{\mathsf A})_{\mathsf A\in\mathrm{Ob}(\ldots)}$.

**Què he fet.** He aplicat aquesta notació a totes les transformacions
naturals del document: unitats, counitats, $\beta^{(m,n)}$, $\theta$, i els
isomorfismes de compatibilitat.

## 16. Demostracions formals de les identitats triangulars

**Comentari.** Demostracions formals, no esquemes, a tot el document.

**Què he fet.**

- Cada identitat triangular és ara una cadena d'igualtats, avaluada en cada
  objecte, amb la justificació de cada pas: definició de la composició
  horitzontal, naturalitat, lema concret.
- On apareix, hi ha la prova de la naturalitat de les transformacions.
- Llocs: `PGdUfAdj`, `PDiscTruncAdj`, `PDiscTruncAdjGl`, `POmegaGdUf`,
  `POmegaDiscTrunc`.

## 17. Sense $\underline{k}$

**Comentari.** Escriure $\min\{k,m\}$ a tot arreu.

**Què he fet.** He substituït totes les aparicions de $\underline{k}$ per
$\min\{k,m\}$.

## 18. Elements dels derivors en `enumerate`

**Comentari.** Per a $\mathbf{Tr}$, $\mathbf{Tr}^{\mathrm{gl}}$,
$\mathbf{Ds}$, $\mathbf{Ds}^{\mathrm{gl}}$ i les versions en $\omega$.

**Què he fet.** A cada definició, els tres components del derivor (la
aplicació de sorts, la d'operacions i els dominis) estan en un `enumerate`,
amb els casos dins de cada component.

## 19. El cas $m=n$

**Comentari.** «Fes un comentari sobre el cas $m=n$.»

**Què he fet.**

- Remarca nova `RTruncDiscCompEqual`: a `PTruncDiscComp` els dos casos se
  solapen quan $m=n$. Hi coincideixen perquè
  $\mathrm{Ds}^{(n,n)}=\mathrm{Tr}^{(n,n)}=\mathrm{Id}$. També diu què
  afirma la proposició en aquest cas.
- Les definicions de $\mathbf{Ds}$ i $\mathbf{Tr}$ fixen explícitament que,
  per a $m=n$, el derivor és la identitat.

## 20. Macros i preàmbul

**Comentari.** Reescriure el codi perquè siga llegible, amb macros com
`\sig{\Sigma}`, i netejar els comandos no usats del preàmbul.

**Què he fet.**

- **Macros noves** (definides al preàmbul, amb comentaris):
  - `\sig{\Sigma}`: signatura en negreta.
  - `\calg{A}`: àlgebra categorial, $\boldsymbol{\mathsf A}$.
  - `\eeq`: igualtat existencial $\overset{\mathrm e}{=}$.
  - `\QE`, `\Dom`, `\id`, `\Id`, `\gd`, `\gl`.
  - `\src`, `\tgt`: font i destí. No es diuen `\sc` i `\tg` perquè `\sc` ja
    és un comando de LaTeX.
  - `\Gd`, `\Uf`, `\Ds`, `\Tr` (functors) i `\bGd`, `\bUf`, `\bDs`, `\bTr`
    (derivors).
- He aplicat les macros a tot el cos del document. **Comprovació:** el text
  del PDF (`pdftotext`) és idèntic abans i després.
- **Comandos eliminats** (no s'usaven): `\comp`, `\bprod`, `\iso`, `\nin`,
  `\uadj`, `\Sub`, `\Sg`, `\Ker`, `\ext`, `\mon`, `\epi` (amb les seues
  caixes) i l'entorn `assumption`. També el comentari `%南通大学`.
- **Mantinc** `showkeys`, que mostra les etiquetes al PDF i és útil mentre
  és un esborrany. Lleva'l quan vulgues.

## 21. Línies comentades

**Comentari.** «Elimina totes les línies del latex que estan comentades.»

**Estat: fet** (commit `d4d5a60`). Ho vas executar tu amb l'ordre de baix;
el text del PDF no ha canviat. Eren 7507 línies (de 12495): l'apèndix
antic, les seccions antigues de derivors i les línies soltes. L'entorn no
em deixa fer aquesta eliminació massiva. Des de l'arrel del repositori,
executa:

```
sed -i '/^[[:space:]]*%/d' scratch/share/higher-order/main.tex
```

Esborra només les línies que comencen per `%`. Les del preàmbul que tenen
un comentari al final (`% signature: \sig{\Sigma}`, …) es conserven. El
fitxer està en git, de manera que és reversible. Després pots compilar per
comprovar-ho.

## 22. Etiquetes

**Comentari.** Revisar que totes les etiquetes tenen sentit.

**Què he fet.**

- **Comprovacions:** no hi ha etiquetes duplicades ni referències
  penjades. Cada prefix correspon a l'entorn: `S` secció, `D` definició,
  `P` proposició, `L` lema, `C` corol·lari o claim, `R` remarca, `F`
  figura, `A` axioma.
- **Canvis de nom:**

  | Abans | Ara | Per què |
  |---|---|---|
  | `SSortedPartial` | `SManySortedSets` | la subsecció és de conjunts multisortals |
  | `DCells`, `PCellsFunctor`, `RCellsFunctorEmpty` | `DDomainSet`, `PDomainSetFunctor`, `RDomainSetEmpty` | defineixen $B_{\mathrm{Dom}^{(\varphi,d)}}$, no cel·les |
  | `SCorestriction` | `SEpRestriction` | la subsecció és la restricció a ep-varietats |
  | `DVarSingleSet`, `DVarGlobular` | `DSpecSingleSet`, `DSpecGlobular` | defineixen especificacions |
  | `RGenHepDerivor` | `RGenHepDerivorCases` | la remarca tracta casos particulars |
  | `DVarSingleSet…`, `DVarGlobularE…` (axiomes) | `ASingleSet…`, `AGlobular…` | són axiomes, no definicions |

- **Etiquetes eliminades:** `C1`–`C5`, `Ci`, `Cii`, `2C1`–`2C3`, a les
  condicions de les categories single-set. No es referenciaven i, posades
  després d'un `\item[...]`, apuntaven al comptador de la secció.

---

## Decisions que has de revisar

1. **`PTransformedAlg`:** he tret «unique» de l'enunciat que proposaves,
   perquè així no és cert (apartat 5).
2. **Ep-àlgebres febles:** són una noció nova, necessària per a la
   construcció de Grothendieck (apartat 9). Mira si t'agrada el nom
   «weak ep-algebra».
3. **Àlgebres de Hall:** les he incloses als preliminars perquè els
   derivors de Curry-Howard s'hi defineixen.
4. **Satisfacció de les E-equacions:** s'expressa amb les operacions terme
   $P^{\mathbf A}$, no amb la presentació de Schmidt de l'esborrany antic.
5. **Functorialitat de $\downarrow\mathbf s$:** l'he omesa, perquè el
   document no la usa.
6. **Bibliografia `CVCLRM26`:** l'entrada nova no té número d'arXiv.
   Completa-la.
7. **«A note from the authors» i els agraïments:** encara parlen del
   document Curry-Howard. No els he tocat.
8. **Proves esquemàtiques:** algunes proves que certs axiomes «esdevenen
   trivials» en la discretització continuen sent esquemàtiques. No són
   identitats triangulars, però potser les vols més formals.
9. **El paràgraf sobre $e^\sharp[H]$:** l'havies editat tu. L'he mogut al
   lloc on s'usa i n'he corregit la notació. Comprova que diu el que volies.
10. **Unificació en $\omega$:** la introducció diu que no l'indueix cap
    derivor hep generalitzat i que s'obté com a límit inductiu, tal com
    explica `RUfOmegaNotDerivor`.
11. **Introducció i abstract:** són una proposta. Revisa'n sobretot la
    motivació (els sistemes de reescriptura i Curry-Howard d'ordre
    superior) i les referències que hi cite: [Str87], [abgmmm23], [Rei87],
    [pb86], [pb02], [CVST10b], [LG18], [CVCL16], [CVCL18], [CVCL23],
    [CVCLRM26].

## Equacions massa llargues

Caixes que sobresurten del marge més de 20pt, amb la línia de `main.tex` (abans
d'esborrar els comentaris) i l'entorn més proper:

| Sobresurt | Línia | Entorn |
|---|---|---|
| 99pt | 4495 | `PDiscTruncAdjGl` |
| 81pt | 3115 | `RGlobularIdent` |
| 80pt | 5530 | `POmegaDiscTrunc` |
| 59pt | 4914 | `DTruncationOmegaGl` |
| 59pt | 5022 | `DDiscretizationOmegaGl` |
| 58pt | 4326 | `LDiscTruncCounit` |
| 57pt | 3684 | `CGradUnifA` |
| 53pt | 915 | `PLaxGConst` |
| 51pt | 2505 | `DSigmaCatSingleSet` |
| 51pt | 5469 | `POmegaDiscTrunc` |
| 50pt | 4988 | `PDiscOmegaDerivor` |
| 49pt | 4346 | `PDiscTruncAdj` |
| 49pt | 4876 | `PTruncOmegaDerivor` |
| 45pt | 3866 | `PGdUfAdj` |
| 40pt | 4086 | `LDiscGlDescription` |
| 39pt | 836 | `DGConst` |
| 38pt | 5366 | `CUfOmegaC` |
| 37pt | 4516 | `PDiscTruncAdjGl` |
| 35pt | 3540 | `PUnifDerivor` |
| 34pt | 1797 | `DDomainSet` |
| 33pt | 432 | `PTermChar` |
| 32pt | 3526 | `PUnifDerivor` |
| 31pt | 4514 | `PDiscTruncAdjGl` |
| 30pt | 1790 | `DDomainSet` |
| 30pt | 5122 | `CLimitNat` |
| 29pt | 5302 | `LUfOmegaCells` |
| 28pt | 2172 | `PHepComp` |
| 27pt | 5522 | `POmegaDiscTrunc` |
| 26pt | 3003 | `DSpecGlobular` |
| 25pt | 2843 | `DOmegaCatGl` |
| 25pt | 4093 | `LDiscGlDescription` |
| 24pt | 3863 | `PGdUfAdj` |
| 24pt | 4087 | `LDiscGlDescription` |
| 23pt | 2200 | `PHepComp` |
| 23pt | 3849 | `CGdUfEquiv` |
| 21pt | 4308 | `LDiscTruncCounit` |
| 20pt | 3738 | `CGradUnifD` |

Moltes es deuen a l'eliminació de les abreviatures (apartat 14). Es poden
partir amb `multline` o `align` quan decidisques el format final.

---

# Notació $\boldsymbol{\mathcal{E}}$ per a les especificacions

Data: 2026-10-19. Commit `0d04a30`.

- **Macro nova:** `\spec{E}` $=\boldsymbol{\mathcal{E}}$, al costat de `\sig`
  i `\calg`.
- **`DEpSpec`:** l'ep-especificació $(\mathbf{\Sigma},\mathcal{E})$ s'escriu
  simplement $\boldsymbol{\mathcal{E}}$. Allà on s'introdueix una especificació es dona
  explícitament, $\boldsymbol{\mathcal{E}}=(\mathbf{\Sigma},\mathcal{E})$ i
  $\boldsymbol{\mathcal{F}}=(\mathbf{\Lambda},\mathcal{F})$ (`DEpVariety`, la correstricció i la
  remarca que la segueix); després només s'usa $\boldsymbol{\mathcal{E}}$:
  $\mathcal{V}(\boldsymbol{\mathcal{E}})$, $\mathsf{EPAlg}(\boldsymbol{\mathcal{E}})$.
- **Especificacions categorials:** $\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}}$ i
  $\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{\mathrm{gl}(n)}}$ (`DSpecSingleSet`, `DSpecGlobular` i el
  cas globular $\omega$) eren quàdruples $(S,\Sigma^{(n)},V^{S},\mathcal{C})$;
  ara són els parells $(\mathbf{\Sigma}^{(n)},\mathcal{C}^{\mathbf{\Sigma}^{(n)}})$,
  com demana `DEpSpec`. Totes les aparicions de
  $\mathsf{EPAlg}(\mathbf{\Sigma}^{(n)},\mathcal{C}^{\mathbf{\Sigma}^{(n)}})$ i
  semblants (98 en total) passen a $\mathsf{EPAlg}(\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(n)}})$.
- **Sense canvis:** les especificacions dels preliminars, que no són
  ep-especificacions: la finitària $(S,\Sigma,\mathcal{E})$, la de Hall
  $\mathrm{H}_{S}$ i les $\mathrm{QE}$-especificacions $(S,\Sigma,X,\mathcal{E})$
  amb $\mathrm{Mod}_{\Sigma}(\mathcal{E})$. Tampoc
  $(\mathbf{\Sigma},\varnothing)$ ni $\mathsf{EPAlg}(\mathbf{\Sigma})$.

Decisions que has de revisar:

1. $\boldsymbol{\mathcal{U}}$ (l'univers) i $\boldsymbol{\mathcal{K}}$ (una
   classe d'àlgebres, `DQEEq`) tenen la mateixa tipografia que les
   especificacions. No s'hi confonen, però si vols pots canviar-ne una.
2. Si vols, les $\mathrm{QE}$-especificacions dels preliminars també es poden
   escriure en negreta.

---

# Operacions de $\Lambda$ i lletres dels derivors

Data: 2026-10-19. Commits `0dd5d64` i `e31011f`.

- **Operacions de $\Lambda$:** s'escriuen $\tau$, perquè $\lambda$ és la
  paraula buida. Només apareixien a `LTermComp`.
- **Derivors:** comencen per $\mathbf{c}$. On abans hi havia $\mathbf{d}$,
  $\mathbf{e}$, $\mathbf{g}$ (amb components $(\varphi,d)$, $(\psi,e)$,
  $(\chi,g)$) ara hi ha $\mathbf{c}$, $\mathbf{d}$, $\mathbf{e}$ (amb
  $(\varphi,c)$, $(\psi,d)$, $(\chi,e)$): als preliminars (`DDerivor`,
  `DDerCompId`, `RDerivorTerms`), a tota la secció de derivors hep
  generalitzats, a la nota de notació de la graduació i a
  `RUfOmegaNotDerivor`. L'associativitat (`PHepSigCat`, (Der4), (L2)) usa
  $\mathbf{c}$, $\mathbf{d}$, $\mathbf{e}$.
- **Sense canvis:** els homomorfismes $f$, $g$; l'element $e$ del monoide
  $\{e,f\}$ de `RUfOmegaNotDerivor`; els noms $\mathsf{Sig}_{\mathfrak{d}}$
  i $\mathsf{Alg}_{\mathfrak{d}}$.
- **Cel·les:** a `PHepComp` i a la nota que la segueix, les cel·les de
  $\mathbf{C}$ es deien $c$, que ara és la component del derivor
  $\mathbf{c}$; ara es diuen $x$. A `LTermComp` les famílies
  $\mathbf{c}$ de $\mathbf{C}$ es mantenen, perquè allà l'únic derivor és
  $\mathbf{d}$.

---

# Principi d'inducció bem fundada

Data: 2026-10-19. Commit `2072b78`.

- **`PPWFI` (nova):** «Principle of Proof by Well-Founded Induction», just
  després de `DHepSignature`, amb l'estil de `PPAI`: per demostrar que tot
  símbol d'operació d'una hep-signatura té una propietat, n'hi ha prou amb el
  pas d'inducció «si tot $\tau\lhd\sigma$ la té, $\sigma$ la té».
- **Nota que la segueix:** no cal cas base, perquè per als símbols
  $\lhd$-minimals (sense símbols d'operació a les condicions de domini) la
  hipòtesi és buida; i el mateix per a la recursió bem fundada.
- **Referències:** les sis demostracions per inducció o recursió al llarg de
  $\lhd$ (`PTransformedAlg`, `PGenHepDerivorHom`, `LSameCells`, `PHepId`
  i les dues parts de `PHepComp`) remeten a
  `PPWFI`.

---

# Dimensió $\omega$ a part, `PSingleSetEp`/`PGlobularEp` i canvi de signatura

Data: 2026-10-19. Commits `ae0d777` i `3d3fa35`.

## Dimensió $\omega$ per separat

- `DSpecSingleSet` és ara només per a $n\in\mathbb{N}$. Just després hi ha
  un paràgraf que defineix $\boldsymbol{\mathcal{C}}^{\mathbf{\Sigma}^{(\omega)}}$
  (axiomes (A0), (A$^k$1)–(A$^k$8) per a $k\in\omega$ i (AB$^{l,k}$1)–(AB$^{l,k}$3)
  per a $l<k$ en $\omega$), com ja es feia en el cas globular.
- La identificació d'àlgebres i àlgebres parcials es fa per a $n\in\mathbb{N}$
  i, a part, per a $\omega$ (single-set i globular).
- La nota sobre les immersions $\Sigma^{\mathrm{gl}(n)}\to\Sigma^{\mathrm{gl}(m)}$
  separa el cas $m\in\mathbb{N}$ del cas $\omega$.
- L'abstract ja no diu «$n\in\mathbb{N}\cup\{\omega\}$»: parla de les àlgebres
  $n$-categorials, per a $n\in\mathbb{N}$, i de les globulars $\omega$-categorials.
  Ja no queda cap «$\mathbb{N}\cup\{\omega\}$» al document.

## `PSingleSetEp` i `PGlobularEp` eliminades

El seu contingut passa a l'última frase de `RSingleSetIdent` i de
`RGlobularIdent`: els símbols amb condicions de domini buides són totals per
(A0)/(A$^k$1) (resp. (EA0)/(EA$^{j,k}$1)), i (A$^k$3) (resp. (EA$^{j,k}$3)) diu
que el domini de la composició és el que fixa la seua condició de domini. Per
tant, els objectes de $\mathsf{EPAlg}$ de l'especificació són exactament els
seus models. `PFiniteDimNotQE` usa aquest fet en dimensió $\omega$, i les
remarques el cobreixen.

## Secció nova: `SChangeSig` (Change of signature)

Al final del document, després de l'square algebraic.

- **`DChangeSigDerivor`:** per a un derivor $\mathbf c=(\varphi,c)$ entre
  signatures heterogènies, $\mathbf c^{(n)}=(\varphi,c^{(n)},\varnothing)$ de
  $\mathbf\Sigma^{(n)}$ a $\mathbf\Lambda^{(n)}$ i
  $\mathbf c^{\mathrm{gl}(n)}$ de $\mathbf\Sigma^{\mathrm{gl}(n)}$ a
  $\mathbf\Lambda^{\mathrm{gl}(n)}$: tradueixen $\sigma$ per $c(\sigma)$ (resp.
  $\sigma_k$ per $c(\sigma)_k$, la còpia de dimensió $k$ del terme) i deixen
  igual l'estructura categorial. Per a $n=0$, $\mathbf c^{(0)}=\mathbf c$.
- **`LTermFunctor`:** les operacions terme d'una àlgebra categorial són
  functors d'ordre superior (inducció sobre termes).
- **`PChangeSigDerivor`:** els functors induïts envien àlgebres $n$-categorials
  de $\mathbf\Lambda$ a àlgebres $n$-categorials de $\mathbf\Sigma$, amb
  descripció explícita.
- **`LChangeSigTerms`:** com es tradueixen $P$ i $P_k$ per
  $\mathbf d^{(n)}$, $\mathbf d^{\mathrm{gl}(n)}$, Gd, Uf, Ds i Tr (via (Der4)).
- **`PChangeSigCat`:** $(\mathbf d\circ\mathbf c)^{(n)}=\mathbf d^{(n)}\circ\mathbf c^{(n)}$
  i identitats, també globulars; per tant, $\mathbf\Sigma\mapsto\mathsf{nCatAlg}(\mathbf\Sigma)$
  és una categoria indexada escindida sobre $\mathsf{Sig}_{\mathfrak d}$.
- **`LCommSquare`:** la conseqüència de `PHepComp` (2) que s'usa per comparar
  composicions.
- **`PChangeSigGdUf`, `PChangeSigDsTr`:** igualtats de derivors hep
  generalitzats i, per tant, igualtats estrictes de functors:
  $\mathrm{Gd}_\Sigma\circ\mathbf c^{(n)*}=\mathbf c^{\mathrm{gl}(n)*}\circ\mathrm{Gd}_\Lambda$,
  $\mathrm{Uf}_\Sigma\circ\mathbf c^{\mathrm{gl}(n)*}=\mathbf c^{(n)*}\circ\mathrm{Uf}_\Lambda$,
  i el mateix per a Ds i Tr en les dues presentacions.
- **`RChangeSigNat`:** $\theta$, $\beta^{(m,n)}$, $\varepsilon$ i
  $\varepsilon^{\mathrm{gl}}$ també són compatibles; per tant, ho són les
  adjuncions i el quadrat algebraic. Al final, una nota mostra que Gd, Uf, Ds i Tr
  s'estenen a les construccions de Grothendieck.
- **Dimensió $\omega$:** `DChangeSigDerivorOmega`, `PChangeSigOmega`,
  `PChangeSigOmegaDsTr` i `PChangeSigOmegaGdUf`. La de Gd es prova per la
  unicitat de la propietat universal; la de Uf, comparant els límits inductius.

Decisions que has de revisar:

1. Has escrit «dues hep-signatures», però $\Sigma^{(n)}$ i
   $\Sigma^{\mathrm{gl}(n)}$ només estan definides per a signatures
   heterogènies (sense condicions de domini). Per això la secció parteix d'un
   derivor entre signatures heterogènies.
2. He anomenat el derivor $\mathbf c$, i no $\mathbf d$, segons la convenció
   nova (els derivors comencen per $\mathbf c$); en les composicions apareix
   $\mathbf d$.
3. `RChangeSigNat` i la nota sobre Grothendieck estan justificades de forma
   breu, no amb una demostració completa. Si vols, es poden convertir en
   proposicions amb prova.

**Respostes (2026-10-19):** (1) una signatura heterogènia és la
hep-signatura amb dominis buits, i no cal la generalització a hep-signatures
amb condicions de domini; (2) es manté $\mathbf c$; (3) `RChangeSigNat` i la
nota sobre Grothendieck queden com estan.

---

# `SEpRestriction` comentada

Data: 2026-10-19. Commit `095a135`.

- La subsecció «Restriction to ep-varieties», amb la remarca
  `RGenHepDerivorCases`, està comentada (línies amb `%`).
- El punt (1) de la remarca, que un derivor indueix el functor usual entre
  àlgebres totals, s'usava tres vegades: ara és dins de `RHepAlgCat`, i les
  referències de la secció de canvi de signatura apunten allà.
- L'exemple del punt (2) ja és `RGradNotEp`, que és on remet ara el paràgraf
  previ a `PGenHepDerivorFunctor`.
- La introducció de la secció `SGraduation` remet només a `DCorestriction`.

---

# Estil de PathMain i neteja del codi

Data: 2026-10-19. Commits `b6ec836` (les teues edicions), `f71c12c`, `c505e48`,
`98e9b6d` i `dfdb840`.

## Què he comparat

He llegit el codi de `Curry_Howard/PathMain.tex` (els capítols de les parts 0–2)
i el de `Projecte Investigador/main.tex`. El preàmbul (estils de teorema, macros),
les cadenes «The following chain of equalities holds» amb «The first equality
…; finally, the last equality …», les afirmacions amb «Claim … follows.» i
«This completes the proof.» ja seguien PathMain. Les teues edicions d'avui han
marcat la resta.

## Canvis d'estil

- **Parells de fórmules:** totes les fórmules «A \qquad and \qquad B» que
  quedaven són ara enumeracions «A; and / B.», amb (TI1)–(TI2) per a les
  identitats triangulars (també a `DAdj`). N'he deixat dues: la de dins d'un
  ítem de `DGradDerivor` i la de «Therefore both … are homomorphisms», que
  quedarien estranyes.
- **Quatre igualtats** en dues columnes (`PChangeSigDsTr`,
  `PChangeSigOmegaDsTr`) passen a ser una enumeració.
- **Cadenes llargues:** `flushleft` amb el membre esquerre a part, com fas tu.
  He partit en línies les igualtats encadenades que sortien del marge.
- **«if, and only if,»** a tot arreu (n'hi havia 8 sense comes).
- **Línies fora del marge:** n'hi havia 71; ara només en queda una d'1pt.
  He afegit `\emergencystretch`, que resol les fórmules en línia que TeX no pot
  tallar, i he arreglat les restants a mà.

## Neteja del codi

- Una frase per línia a la prosa. És el canvi més gran, però no altera el PDF
  (comprovat caràcter a caràcter) i fa que els diffs de git siguen llegibles.
- Un sol `\allowdisplaybreaks` al preàmbul, en lloc dels 101 que hi havia.
- Fora els espais al final de línia i les línies en blanc repetides.

## No he tocat

Les etiquetes (la biblioteca hi remet) i la subsecció comentada
`SEpRestriction`.

---

# Propostes B–H, estil d'enunciats i proves, i versió compacta

Data: 2026-10-19. Commits `c458707`–`8ba67e6` (`main.tex`) i `f46d3fa`
(`article.tex`).

## `main.tex` (de 112 a 95 pàgines)

- **B.** La secció 3 acaba amb $\mathsf{hepSig}_{\mathfrak{gd}}$
  (`PHepSigCat`). La construcció de Grothendieck laxa dels preliminars i la
  subsecció de $\mathsf{hepAlg}_{\mathfrak{gd}}$ estan comentades. La remarca
  `RHepAlgCat`, nova, n'explica la construcció en poques línies.
- **C.** Les àlgebres de Hall estan comentades. $c^\sharp$ es defineix per
  recursió sobre termes amb (Der1)–(Der2), i (Der4) es demostra
  (`LDerSubst`, `PSigdCat`).
- **E.** Les comprovacions d'axiomes de `PGradDerivor` i `PUnifDerivor` són
  ara una llista amb un càlcul representatiu.
- **F.** Discretització i truncació: un sol enunciat per als casos single-set
  i globular. Les etiquetes `...Gl` desapareixen i les referències apunten a
  l'etiqueta single-set. Les seccions 8 i 9 són ara una sola.
- **G.** Les identitats triangulars s'enuncien com «$\Tr(\varepsilon)$ i
  $\varepsilon_{\Ds}$ són identitats», amb una prova d'un paràgraf.
- **H.** El canvi de signatura en dimensió $\omega$ queda resumit a
  `RChangeSigOmega`; el detall està comentat.

## Estil d'enunciats i proves (comparat amb PathMain)

- Els enunciats de PathMain són més curts (mediana de 35 paraules, davant de
  51 als nostres). Una convenció després de `DGenHepDerivor` fixa els noms
  dels components de signatures i derivors, i els enunciats ja no els
  repeteixen.
- A PathMain, `\textsf{(...)}` només numera apartats: (1), (2), (i)…. Els
  passos s'anuncien amb frases: «We first prove…», «Now we prove…», «Next,
  …», «Finally, …». Els 92 rètols amb nom que havia posat jo, com «(Ep-algebra)»
  o «(Axioms)», ara són frases. Els numerats, com (D1), (H$_\sigma$1) o
  «(1) implies (2)», es mantenen.
- La llargària mitjana de les frases a les proves ja era semblant (14 paraules,
  davant de 15,5 a PathMain).

## `article.tex`, versió compacta (20 pàgines)

Fitxer nou, amb els mateixos resultats que `main.tex`:
- preliminars reduïts a la notació;
- les àlgebres categorials definides directament pels axiomes (només en forma
  de fórmula), amb una remarca que en remet a la noció usual;
- casos single-set i globular sempre junts;
- comprovacions rutinàries resumides en una frase;
- dimensió $\omega$ tractada a part.

Les proves conserven tots els passos lògics, però deixen al lector les
comprovacions mecàniques.

# Proposicions seguides de corol·laris (estil Curry-Howard)

Data: 2026-10-20. Commits `4e0d71e`, `ad7437a`, `1630430` i `b0db19a`.

## Què he comparat

A les parts 1 i 2 de `Curry_Howard` hi ha 243 proposicions i 83 corol·laris
(aproximadament un corol·lari per cada tres proposicions); a `main.tex` n'hi
havia 60 i 5. Quan un enunciat diu «Consequently, …», «In particular, …» o
«Thus …» i afegeix un segon resultat, a Curry-Howard aquest segon resultat és
un corol·lari, introduït per una frase («From the above proposition we
obtain …») i amb una prova curta que cita la proposició. Ara `main.tex` té 60
proposicions i 23 corol·laris. Cap resultat no canvia: només es reparteixen els
enunciats i les proves.

## Proposició + corol·lari

| Proposició (es queda amb) | Corol·lari nou (passa a dir) |
| --- | --- |
| `PSigdCat`: les tres igualtats sobre $c^\sharp$ | `CSigdCat`: $\mathsf{Sig}_{\mathfrak{d}}$ és una categoria |
| `LTermComp`: el valor de $d^\sharp(P)$ | `CTermComp`: la conseqüència per a les E-equacions |
| `PHepId`: $(\id)^{\ast}_{\gd}$ deixa igual àlgebres i homomorfismes | `CHepId`: indueix el functor identitat |
| `PHepComp`: la inclusió $\kappa^{\mathbf{c},\mathbf{d}}$ i la seua naturalitat | `CHepComp`: l'antic apartat (2), quan els dos functors coincideixen |
| `PFiniteDimNotQE`: no hi ha cap conjunt de QE-equacions | `CFiniteDimNotQE`: subcategoria plena pròpia |
| `PUnifGrad`: $\bGd\circ\bUf=\id$ | `CUnifGrad`: $\Uf\circ\Gd=\Id$ |
| `PDiscComp`: igualtats de derivors | `CDiscComp`: igualtats de functors |
| `PDiscOmegaDerivor`: corestriccions | `CDiscOmegaDerivor`: les cel·les tenen dimensió finita |
| `POmegaGdUf`: els dos isomorfismes naturals | `COmegaGdUfEquiv`: equivalències i equivalència adjunta |
| `PChangeSigCat`: igualtats de derivors | `CChangeSigCat`: igualtats de functors; `CChangeSigIndexed`: categories indexades escindides (abans, un paràgraf) |
| `PChangeSigGdUf`, `PChangeSigDsTr`: igualtats de derivors | `CChangeSigGdUf`, `CChangeSigDsTr`: igualtats de functors |

Els antics `Claim`s de `PChangeSigGdUf` i `PChangeSigDsTr` (igualtat de
derivors / igualtat de functors) són ara la prova de la proposició i la del
corol·lari.

## Paràgrafs que ara són corol·laris

Els paràgrafs «By Proposition … and Remarks … the restriction … corestricts
…, and, by abuse of notation, we denote …» són ara corol·laris, seguits de la
notació: `CGradFunctor`, `CUnifFunctor`, `CDiscFunctor`, `CTruncFunctor` i
`CChangeSigFunctor`.

## Altres canvis

- `CGdUfEquiv` va ara després de `PGdUfAdj`, com a corol·lari seu, i també
  diu que l'adjunció és una equivalència adjunta (abans, «Thus it is an
  adjoint equivalence» dins de la proposició).
- Les cites apunten al resultat que fan servir: per exemple, «Proposition
  `PHepComp`~(2)» és ara «Corollary `CHepComp`», i les identitats
  $\Ds^{(n,n)}$, $\Tr^{(n,n)}$ citen `CHepId`.
- La introducció de la secció 3 descrivia subseccions que ja estan comentades
  (`SEpRestriction` i la construcció de Grothendieck laxa); ara descriu el que
  hi ha.
- Una frase repetida a la prova de `PUnivPropCatAlg` («This does not depend on
  $n$»).
- Frases d'entrada abans de `CGenHepDerivorDiagram`, `DGraduation`,
  `DUnification`, `PDiscComp` i `CLimitNatGl`.

## Què no he canviat

- Les observacions que contenen resultats (`RSingleSetIdent`,
  `RGlobularIdent`, `RDiscOmegaTrunc`, …): a Curry-Howard, la igualtat
  $\mathsf{PAlg}(\ldots)=\mathsf{nCatAlg}(\Sigma)$ també és una observació.
- `PUfOmega` («Moreover, $\Uf^{(\omega)}$ is a functor»): la naturalitat de
  $\mathrm{in}^{[n]}$, que és a l'enunciat, ja necessita el functor, i
  separar-los demana reordenar la prova.
- `PTruncComp`: la igualtat de functors single-set no es dedueix de cap
  igualtat de derivors, i per tant no és un corol·lari.
- Els preliminars, copiats de Curry-Howard, i `article.tex`.

El document compila sense errors ni referències indefinides (97 pàgines).
