val args = CommandLine.arguments();
val inputfile = List.nth(args,0);
val outfile = List.nth(args,1);

CM.make "run.cm";

Prop.parse(inputfile,outfile);