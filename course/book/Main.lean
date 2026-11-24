import VersoManual
import TauBook

open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main := manualMain (%doc TauBook) (config := { config with })
