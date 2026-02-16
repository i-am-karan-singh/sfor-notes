#let lecturetitle(title, number) = {
  align(center)[
    #box(
      inset: 1em,
      stroke: black
    )[
      *47-837: Statistical Foundations of OR* #h(1fr) Lecture #number
      
      #text(size: 1.5em)[
        #title
      ]
      
      #h(1fr) Lecturer: Karan Singh
    ]
    #v(1em)
  ]
}

#let lecture(title, number, doc) = {
  set page(paper: "us-letter")
  set heading(numbering: "1.")
  set text(font: "New Computer Modern")
  set par(justify: true)
  
  show heading: set block(above: 1.4em, below: 1em)
  
  let citet(key) = cite(key, form: "prose")

  lecturetitle(title, number)
  
  doc
}