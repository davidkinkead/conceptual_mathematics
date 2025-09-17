namespace ConceptualMathematics.Html

def cmCss : Array (String × String) := #[("cm.css", r#"
div.definition, div.excerpt, div.question, div.proof {
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  margin: 1rem 0 1rem 0;
  padding: 1rem;
}

div.print {
  color: blue;
}

span.definitionTerm, span.excerptTitle, span.questionTitle, span.proofTitle {
  font-family: sans-serif;
  font-size: larger;
  font-weight: bold;
}

details.solution {
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  margin: 1rem 0 1rem 0;
  padding: 1rem;
}

summary.solution {
  font-style: italic;
}
"#)]

end ConceptualMathematics.Html
