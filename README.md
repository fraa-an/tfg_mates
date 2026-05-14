### Ejemplo:
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
