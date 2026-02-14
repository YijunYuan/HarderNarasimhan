Please add comments to every Lean file in this folder and its subfolders. The requirements are as follows:

At the beginning of each file (note: the comment must be placed after the import section; otherwise, placing it at the very top of the file will cause errors), add a comment block introducing the main purpose of the file. In particular:

All files named Defs.lean correspond to the definitions of concepts in that module (as well as a small number of basic properties).

Impl.lean files correspond to the concrete implementation of that module and are generally not user-facing.

Results.lean files correspond to the main results of that module.

Before every lemma, theorem, definition, class, structure, and instance, add a comment block explaining:

The mathematical meaning of the corresponding code (in natural language), and

Its API design considerations as formalized code.

This project essentially corresponds to the paper in the attached file HNGame.pdf, which you may consult for reference. You may notice that some parts of the formalized code differ slightly from the statements in the paper. On the one hand, this is due to design decisions made during formalization; on the other hand, there are a few minor errors in the paper that have been corrected in the code. In such cases, the comments should follow the code rather than the paper.

The comments must be detailed and professional. Each comment block should begin with /- (not /--) and end with -/.

All comments must be written in English. This is very important.