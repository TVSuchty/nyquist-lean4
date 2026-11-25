# Das Nyquist-Stabilitätskriterium in Lean 4 – erklärt für E-Technik- & Informatik-Studierende

*(Zielgruppe: Bachelor / FH – Elektrotechnik, Mechatronik, Automatisierungstechnik oder Informatik mit Grundkenntnissen in Regelungstechnik und Analysis.)*

> **Ehrlicher Disclaimer:** Ich (der Repo-Ersteller) habe zwar ein bisschen Regelungstechnik in meinem Leben gemacht, aber was hier mathematisch und in Lean 4 abgeht, ist ehrlich gesagt weit über meinem Niveau. Praktisch der gesamte Code, alle Beweise und auch diese Erklärung wurden komplett von KI erstellt – ich habe im Wesentlichen nur ein bisschen gepromptet. Die mathematische Korrektheit ist trotzdem hart abgesichert, weil der Lean-4-Kernel jeden einzelnen Beweisschritt ohne `sorry` und ohne Zusatzaxiome maschinell nachgeprüft hat.

---

## 1. Worum geht es überhaupt?

In der **Regelungstechnik** schließt man eine Strecke $G(s)$ mit einem Regler $C(s)$ zu einem offenen Kreis $L(s) = C(s)G(s)$ zusammen und führt den Ausgang zurück (Einheitsrückkopplung). Der geschlossene Regelkreis hat dann die Übertragungsfunktion:

$$T(s) = \frac{L(s)}{1 + L(s)}.$$

Die große Frage lautet: **Ist der geschlossene Regelkreis stabil?**
Mathematisch bedeutet Stabilität bei linearen Systemen: **Alle Pole von $T(s)$** – also alle Nullstellen von $1 + L(s)$ – müssen in der **offenen linken Halbebene** liegen ($\operatorname{Re}(s) < 0$), weil Terme wie $e^{s t}$ nur dann abklingen.

Das Problem:
* Für ein Polynom 10. Grades die Nullstellen auszurechnen ist lästig;
* wenn ein System eine **Totzeit** $e^{-\tau s}$ hat (z. B. Transportband, Rohrleitung, Funkverzögerung), ist $1 + L(s)$ gar kein Polynom mehr – dann versagen Routh-Hurwitz & Co. komplett!

**Harry Nyquists Trick (1932):**
Statt die Pole in der rechten Halbebene zu suchen, fährst du nur die Frequenzachse $s = i\omega$ ($\omega$ von $-\infty$ bis $+\infty$) entlang und zeichnest die Ortskurve $L(i\omega)$ in der komplexen Ebene. Dann zählst du, wie oft die Ortskurve den kritischen Punkt **$-1$** umrundet!

Die Formel lautet:
$$N_{\text{CCW}} = P - Z \qquad \text{bzw.} \qquad N_{\text{CW}} = Z - P$$

* **$P$** (`rhpRootCount D`): Anzahl der **instabilen Pole des offenen Kreises** (im rechten Halbraum $\operatorname{Re}(s) > 0$).
* **$Z$** (`rhpRootCount (D + N)`): Anzahl der **instabilen Pole des geschlossenen Kreises**.
* **$N_{\text{CCW}}$ / $N_{\text{CW}}$**: Wie oft $L(i\omega)$ den Punkt $-1$ gegen bzw. im Uhrzeigersinn umrundet.
* **Stabilität ($Z = 0$):** Der geschlossene Kreis ist genau dann stabil, wenn er $-1$ **genau $P$-mal gegen den Uhrzeigersinn** (also $-P$-mal im Uhrzeigersinn) umrundet. Ist der offene Kreis schon stabil ($P = 0$), darf $-1$ überhaupt nicht umrundet werden ($N = 0$).

---

## 2. Warum das Ganze in „Lean 4“ formalisieren?

Normalerweise rechnet man sowas mit MATLAB, Python oder auf Papier durch. Warum also **Lean 4**?

Lean 4 ist kein Numerik-Tool, sondern ein **mathematischer Beweisassistent**. Jede Definition, jedes Integral, jede Grenzwert-Abschätzung und jede Fallunterscheidung wird von einem winzigen, vertrauenswürdigen Typentheorie-Kernel Zeile für Zeile überprüft. Wenn Lean am Ende `Build completed successfully` sagt und kein `sorry` im Code steht, ist der Beweis **logisch lückenlos** – kein vergessener Sonderfall, kein Vorzeichenfehler, keine Rundungsungenauigkeit.

---

## 3. Was genau in diesem Projekt abgeht (Modul für Modul)

### A. Grundbegriffe (`Nyquist/Defs.lean`)
Hier werden die Vokabeln der Regelungstechnik in Lean definiert:
* `evalTransfer N D s := N(s) / D(s)` für rationale Übertragungsfunktionen $L(s) = N(s)/D(s)$.
* `IsHurwitz p`: Polynom $p \neq 0$, alle Nullstellen haben $\operatorname{Re}(z) < 0$.
* `nyquistCurve N D ω := L(iω)` (die Ortskurve) und `returnDifference N D s := 1 + L(s)`.
* `nyquistEncirclementsCCW` / `CW`: Die Umrundungszahl mathematisch exakt definiert als Kurvenintegral der logarithmischen Ableitung:
  $$N_{\text{CCW}} = \frac{1}{2\pi i} \int_{-\infty}^{+\infty} \frac{\frac{d}{d\omega}(1 + L(i\omega))}{1 + L(i\omega)}\,d\omega.$$
  Warum misst das Integral Umrundungen? Weil $\frac{d}{d\omega}\ln(z(\omega)) = \frac{z'(\omega)}{z(\omega)}$: Der Realteil ($\ln|z|$) hebt sich von $-\infty$ bis $+\infty$ weg, und der Imaginärteil ($i \cdot \varphi(\omega)$) zählt genau den aufsummierten Drehwinkel geteilt durch $2\pi$!

### B. Der klassische rationale Beweis (`LogDeriv`, `ImagAxisIntegral`, `SemicircleIntegral`, `Criterion`)
Hier wird das Nyquist-Kriterium für beliebige rationale $L(s) = N(s)/D(s)$ bewiesen – auf zwei unabhängigen Wegen:
1. **Über Kurvenintegrale (`nyquist_encirclement_formula`, `nyquist_dContour_tendsto`):**
   * `1 + L(s) = (D(s) + N(s)) / D(s)` wird über alle Nullstellen und Pole in Partialbrüche zerlegt:
     $$\frac{(1+L)'}{1+L} = \sum_z \frac{1}{s - z} - \sum_p \frac{1}{s - p}.$$
   * Entlang der imaginären Achse hat jeder einzelne Pol $\frac{i}{i\omega - a}$ eine explizite Stammfunktion aus $\ln$ und $\arctan$ (`poleAntideriv`).
   * Für $R \to \infty$ liefert ein Pol in der rechten Halbebene ($\operatorname{Re}(a) > 0$) exakt $-i\pi$, ein Pol in der linken Halbebene $+i\pi$.
   * Auf dem großen rechten Halbkreis (`SemicircleIntegral.lean`) liefert jeder Pol/Nullstelle $-i\pi$. Bei properen Systemen ($\deg(D+N) = \deg D$) gibt es gleich viele Pole wie Nullstellen, sodass sich der Halbkreis zu **0** wegkürzt!
   * Und warum darf man überhaupt über ganz $(-\infty, \infty)$ integrieren (Lebesgue-Integrierbarkeit)? Weil einzelne Terme $\sim \frac{1}{\omega}$ nicht integrierbar sind, **Differenzen** je einer Nullstelle und eines Pols aber wie $\mathcal{O}(1/\omega^2)$ abfallen (`integrable_pole_sub_ref`).
2. **Über die stetige Phasenfunktion (`PhaseLift.lean`, `nyquist_phase_lift`):**
   * Informatiker und E-Techniker denken bei „Umrundungen“ oft an das **Phase Unwrapping** (stetiger Phasenwinkel $\Phi(\omega)$ ohne $2\pi$-Sprünge).
   * `PhaseLift.lean` baut dieses stetige $\Phi(\omega)$ explizit aus den $\arctan$-Phasen aller Linearfaktoren und beweist mit dem Zwischenwertsatz (`continuous_phase_lift_unique`), dass jede beliebige stetige Phasenhebung denselben Netto-Phasenhub $\Phi(+\infty) - \Phi(-\infty) = 2\pi(P - Z)$ hat.

### C. Allgemeines Argumentprinzip & Satz von Rouché (`Nyquist/ArgumentPrinciple.lean`)
Statt nur Polynome zu betrachten, beweist dieses Modul die großen Klassiker der Funktionentheorie für beliebige **meromorphe Funktionen** direkt auf Mathlib-Infrastruktur (`FactorizedRational`):
* `argumentPrinciple_circle` (Kreise)
* `rouche_circle` (Satz von Rouché – bewiesen ohne Homotopie, direkt über `Complex.log` auf der geschlitzten Ebene)
* `argumentPrinciple_rect` (Rechtecke – wichtig für Totzeitsysteme!)

### D. Integratoren / Pole im Ursprung (`Nyquist/Indentation.lean`)
In der Praxis hat fast jeder PI- oder PID-Regler einen **Integrator** $\frac{1}{s}$ – also einen Pol genau auf der imaginären Achse bei $s = 0$!
* `Indentation.lean` formalisiert die klassische **kleine Ausbuchtung** (Halbkreis mit Radius $\varepsilon \to 0^+$ rechts um den Ursprung).
* Auf dem Beispiel $L(s) = \frac{K}{s(s+1)}$ ($K > 0$) wird gezeigt, dass der geschlossene Kreis stabil ist und die ausgebuchtete Nyquist-Umrundungszahl tatsächlich $0$ ergibt (`example_integrator_stable`).

### E. Totzeitsysteme (`Nyquist/TimeDelay.lean`)
Echter Höhepunkt für die Regelungstechnik: $L_\tau(s) = \frac{N(s)}{D(s)} e^{-\tau s}$ ($\tau \ge 0$).
* Weil $e^{-\tau s}$ keine rationale Funktion ist, hat $D(s) + N(s)e^{-\tau s} = 0$ **unendlich viele Nullstellen**, und Routh-Hurwitz funktioniert nicht mehr.
* `TimeDelay.lean` beweist mit dem Rechteck-Argumentprinzip (`argumentPrinciple_rect`), dass im geschlossenen rechten Halbraum für streng propere Strecken trotzdem nur **endlich viele** Nullstellen liegen können, dass die drei äußeren Rechteckseiten für $R \to \infty$ verschwinden, und liefert sowohl das vollständige **Totzeit-Nyquist-Kriterium** (`nyquist_delay_stability_criterion`) als auch eine **laufzeitunabhängige Small-Gain-Bedingung** (`nyquist_delay_small_gain`) – inklusive des konkreten Beispiels $L_\tau(s) = \frac{1}{s+2}e^{-\tau s}$, das für **alle** $\tau \ge 0$ stabil bleibt!

### F. Small-Gain, Verstärkungsreserve & Pol-Nullstellen-Kürzung (`Nyquist/Margins.lean`)
* **`nyquist_small_gain_hurwitz`:** Bleibt die Ortskurve komplett innerhalb des Einheitskreises ($\|L(i\omega)\| < 1$), kann sie $-1$ nie umschließen → geschlossener Kreis bleibt stabil.
* **`nyquist_gain_margin`:** Wenn eine stabile Strecke für alle Verstärkungen $k \in [0, K_{\max}]$ den Punkt $-1/k$ nicht trifft ($1 + k L(i\omega) \neq 0$), bleibt der geschlossene Kreis auf dem gesamten Intervall stabil (bewiesen über dominierte Konvergenz + Zwischenwertsatz!).
* **`coprime_no_rhp_cancellation`:** Sind $N$ und $D$ teilerfremd (`IsCoprime`), kann es keine versteckten RHP-Pol-Nullstellen-Kürzungen geben.

---

## 4. Und was bedeutet „ZFC-Axiome“?

In der Mathematik ist **ZFC** (Zermelo-Fraenkel-Mengenlehre mit Auswahlaxiom) das Standardfundament. Lean arbeitet zwar intern mit Typentheorie, lässt sich aber mit `#print axioms` abfragen, welche Grundannahmen ein Beweis benutzt.

In diesem Projekt liefert `#print axioms` für **alle** Hauptsätze ausschließlich:
```
[propext, Classical.choice, Quot.sound]
```
Das heißt: Keine selbst erfundenen Axiome, keine ungeprüften Compiler-Tricks (`native_decide`, `Lean.trustCompiler`), kein `sorry`. Diese drei Standardaxiome von Lean entsprechen direkt der klassischen Mengenlehre (Aussagenextensionalität, Auswahlaxiom, Quotientenbildung).
