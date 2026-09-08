# Verificación formal de programas Yul
Este repositorio contiene el código fuente desarrollado como parte del Trabajo de Fin de Grado (TFG) en Matemáticas en la Universidad Complutense de Madrid (UCM), titulado "Verificación formal de programas Yul".

## Descripción del proyecto

El objetivo de este proyecto es la verificación formal de programas del lenguaje **Yul**, utilizado para la programación de contratos inteligentes en la Máquina Virtual de Ethereum (EVM). 

El repositorio incluye la definición del Árbol Sintáctico Abstracto (AST), la semántica operacional y la semántica axiomática del lenguaje.

## Estructura del repositorio

El código fuente del directorio `/FORYU/` contiene las bases sobre las que se construye el proyecto:
* **`dialect.v`**: Formalización base del dialecto de la EVM.
* **`misc.v`**: Requerido por **`dialect.v`**. Incluye utilidades matemáticas y algunos lemas auxiliares.


El código fuente principal se encuentra en el directorio `/main/`, estructurado en los siguientes módulos matemáticos:

* **`ast.v`**: Definición de la sintaxis del lenguaje.
* **`fran_dialect.v`**: Definición del dialecto (incluyendo *opcodes* de la EVM).
* **`parser.v` / `fran_dialect_parser.v`**: Definición del analizador sintáctico del lenguaje.
* **`semantica.v`**: Semántica operacional de paso largo.
* **`hoare.v`**: Semántica axiomática. Define las ternas de Hoare y demuestra la corrección de las reglas de inferencia.
* **`equiv.v`**: Demostraciones de equivalencia estructural y análisis de programas divergentes (bucles infinitos).
* **`tests.v`**: Casos de prueba para todas las instrucciones del lenguaje. Permiten detectar tempranamente errores en la semántica definida, aunque no permiten probar su corrección.
* **`ejemplos.v`**: Ejemplos de evaluación, incluyendo algunos donde se aplican teoremas de **`hoare.v`** para certificar el estado final de programas Yul complejos.

## Requisitos y compilación

Para explorar o compilar las demostraciones de este proyecto es necesario disponer de:
* **Rocq** (versión recomendada: 9.1.0).

Para comprobar las demostraciones, basta con ejecutar el compilador de Rocq en orden de dependencias o abrir los archivos en un entorno compatible. En el desarrollo de este proyecto, se ha utilizado VSCode con **VsRocq** (versión 2.4.3 de vsrocq-language-server).

### Ejemplos de evaluación:
Para ejecutar el parser con el programa "{ let x := 2 }".
 ```
Require Import main.parser.
From Stdlib Require Import Strings.String.
Open Scope string_scope.
Compute parsea_bloque 100 (tokeniza "{ let x := 2 }").
```
Para hacer pruebas de la semántica de paso largo:
```
Compute eval_programa "{ let x := 2 }".
```
