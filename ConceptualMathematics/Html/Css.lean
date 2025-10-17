namespace ConceptualMathematics.Html

def cmCss : Array (String × String) := #[("cm.css", r#"
.todo {
  color: red;
}

code.hl.lean.block {
  background-color: #f2f2f2;
  border: 1px solid #f2f2f2;
  border-radius: 0.5rem;
  margin: 2rem 0 2rem 0;
  padding: 1rem;
}

pre.hl.lean.lean-output.information {
  margin: 0 0 2rem 0;
}

div.definition, div.excerpt, div.proof, div.question {
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  padding: 1rem;
}

div.definition, div.excerpt {
  margin: 2rem 0 2rem 0;
}

div.proof {
  margin: 0 0 2rem 0;
}

div.question {
  margin: 2rem 0 0.5rem 0;
}

span.definitionTerm, span.excerptTitle, span.proofTitle, span.questionTitle {
  font-family: sans-serif;
  font-size: larger;
  font-weight: bold;
}

summary {
  font-family: sans-serif;
}

summary.solution {
  font-style: italic;
}

details {
  padding: 1rem 1rem 1rem 0;
}

details.solution {
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  margin: 0 0 2rem 0;
  padding: 1rem;
}
"#)]

end ConceptualMathematics.Html
