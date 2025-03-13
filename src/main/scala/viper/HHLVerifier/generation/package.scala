package viper.HHLVerifier

/**
 * Viper Code Generation related functionality.
 * This package contains all code related to the generation of new viper code.
 *
 * ==File Structure==
 * - [[viper.HHLVerifier.generation.AxiomParser]] contains code related to parsing and loading axioms for handling
 *   custom composite types.
 *
 * - [[viper.HHLVerifier.generation.Generator]] contains the actual translation process from a Hypra AST to a Viper AST.
 *
 * - [[viper.HHLVerifier.generation.HHLMap]] provides an interface for interacting with the HHLMap domain.
 *
 * - [[viper.HHLVerifier.generation.HHLSeq]] provides an interface for interacting with the HHLSeq domain.
 *
 * - [[viper.HHLVerifier.generation.SetState]] provides an interface for interacting with the SetState domain.
 *
 * - [[viper.HHLVerifier.generation.State]] provides an interface for interacting with the State domain
 *
 * ==Usage==
 * Call `Generator.generate` with a HHLProgram and the source code to generate a Viper AST.
 * This might fail and throw and error.
 */
package object generation {}
