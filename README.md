# Installation
1. Install Z3
2. Clone the project with the command `git clone --recursive https://github.com/anqili426/hhl_frontend.git`

# Running the verifier
## To run in terminal
Enter the following commands: 
- `cd hhl_frontend`
- `sbt "run <path_to_program.txt> <verifier_options>"`\

Note that you might need to specify the path to Z3 using the command `export Z3_EXE=<path_to_z3>`

## To run in IntelliJ
Import the project into IntelliJ and edit the configurations as follows:
- VM options: `-Xss32m`
- Main class: `viper.HHLVerifier.Main`
- Program arguments: `<path_to_program.txt> <verifier_options>`
- Environment variables: `Z3_EXE=<path_to_z3>`


## Verifier options
You may provide the following options as program arguments to customize the verifier:
- `--forall` Only generates overapproximation encodings
- `--exists` Only generates underapproximation encodings
- `--output <path_to_file>` Saves the generated Viper program in the specified file
- `--noframe` Turns off auto-framing
- `--inline` Verifies the loop invariants in an inline fashion when using the whileDesugard rule
- `--auto` Automatically selects the rule to verify loops when the rules are unspecified

# Program syntax
Most of the syntax is the same as Viper syntax. 

## Methods
```
method <method_name> (<parameter_name>: <parameter_type>)
  returns (<return_variable_name>: <return_type>)
  requires <hyper-assertion>
  ensures <hyper-assertion>
{
  <stmt>
}
```

## Loops
```
while <ruleToUse> (<loop_guard>)
invariant <hyper-assertion>
decreases <expression>
{
  <stmt>
}
```
`<ruleToUse>` has 4 possible values: `syncRule`, `syncTotRule`, `forAllExistsRule`, `desugaredRule`.\
When `<ruleToUse>` is unspecified, the verifier will automatically select one from the first 3 above when it is run with the option `--auto`.







   



