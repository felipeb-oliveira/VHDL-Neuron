LIBRARY ieee;
use ieee.numeric_std.all;
use ieee.std_logic_1164.all;
use ieee.fixed_pkg.all;

PACKAGE fixed_package IS
 	CONSTANT MAX_IND : INTEGER := 15;
 	CONSTANT MIN_IND : INTEGER := -15;
 	SUBTYPE fixed_range IS INTEGER RANGE MIN_IND TO MAX_IND;
 	TYPE fixed IS ARRAY (fixed_range RANGE <>) of BIT;
 	TYPE matrix IS ARRAY (fixed_range RANGE <>, fixed_range RANGE <>) of BIT;
  
 	function to_fixed (arg_L: integer; max_range: fixed_range := MAX_IND; min_range: fixed_range := 0) return fixed;
 	function to_fixed (arg_L: real; max_range, min_range: fixed_range) return fixed;
	function to_integer (arg_L: fixed) return integer;
	function to_real (arg_L: fixed) return real;
	function "+"(arg_L, arg_R: fixed) return fixed;
	function "-"(arg_L, arg_R: fixed) return fixed;
	function "+"(arg_L: fixed; arg_R: integer) return fixed;
	function "+"(arg_L: integer; arg_R: fixed) return fixed;
	function "-"(arg_L: fixed; arg_R: integer) return fixed;
	function "-"(arg_L: integer; arg_R: fixed) return fixed;
	function "*"(arg_L, arg_R: fixed) return fixed;
	function "*"(arg_L: integer; arg_R: fixed) return fixed;
	function "*"(arg_L: fixed; arg_R: integer) return fixed;
	function "+"(arg_L: fixed; arg_R: real) return fixed;
	function "+"(arg_L: real; arg_R: fixed) return fixed;
	function "-"(arg_L: fixed; arg_R: real) return fixed;
	function "-"(arg_L: real; arg_R: fixed) return fixed;
	function "*"(arg_L: fixed; arg_R: real) return fixed;
	function "*"(arg_L: real; arg_R: fixed) return fixed;
	
END PACKAGE fixed_package;

PACKAGE BODY fixed_package IS

  	FUNCTION Max (arg_L : INTEGER; arg_R : INTEGER) RETURN INTEGER IS
	 	VARIABLE s : INTEGER;
	BEGIN
		IF (arg_L > arg_R) THEN 
		  s := arg_L;
		ELSE 
		  s := arg_R;
		END IF;
		RETURN s;
	END Max;


	FUNCTION Min (arg_L : INTEGER; arg_R : INTEGER) RETURN INTEGER IS
		VARIABLE s : INTEGER;
	BEGIN
		IF (arg_L < arg_R) THEN
		  s := arg_L;
		ELSE 							
		  s := arg_R;
		END IF;
		RETURN s;
	END Min;

	-- Q format
	-- [0   1   1   1   0   .   0    0    1]
	-- 2^4 2^3 2^2 2^1 2^0     2^-1 2^-2 2^-3

	FUNCTION COMP1_FIXED (arg_L : fixed) RETURN fixed IS
	 	variable s : fixed(arg_L'range);
	BEGIN
		FOR i in arg_L'range LOOP
			s(i) := not arg_L(i);
		END LOOP;
		RETURN s;
	END COMP1_FIXED;


	FUNCTION ADD_SUB_FIXED (arg_L : fixed ; arg_R : fixed; c : BIT) RETURN fixed IS
		variable s : fixed(arg_L'range);
		variable v : BIT := c;
	BEGIN
		FOR i in s'range LOOP
			s(i) := (arg_L(i) XOR arg_R(i) XOR v);
			v := (arg_L(i) AND arg_R(i)) OR (v AND (arg_L(i) OR arg_R(i)));
		END LOOP;
		RETURN s;
	END ADD_SUB_FIXED;

	
	--MULT_FIXED
	function MULT_FIXED (arg_L, arg_R: fixed) return fixed is
		--Os valores de m e n sao obtidos dos sinais a e b a serem multiplicados.
		constant m: integer := arg_L'length;		--Eh sempre igual a 32 para o projeto
		constant n: integer := arg_R'length;		--Eh sempre igual a 32 para o projeto
		alias arg_Lv : fixed(m-1 downto 0) is arg_L;
		alias arg_Rv : fixed(n-1 downto 0) is arg_R;
		
		variable RESULT: fixed(arg_L'RANGE);
			
		-- Variaveis para armazenamento dos dados de entrada e de saida no formato bit_vector
		variable a, b, p: bit_vector(m+n-1 downto 0);
	
		--Primeiro criamos um tipo ?matrix?
		type matrix is array (natural range <>, natural range <>) of bit;

		--Depois criamos as matrizes de interconexao:
		--Mi,j	Mij(i, j)		0 <= i <= m+n-1, 0 <= j <= m+n-1
		variable Mij: matrix(0 to m+n-1, 0 to m+n-1);
		--Ci,j	Cij(i, j)		0 <= i <= m+n-1, 0 <= j <= m+n
		variable Cij: matrix (m+n-1 downto 0, m+n downto 0);
		--Pi,j	Pij(i, j) 	0 <= i <= m+n, 0 <= j <= m+n
		variable Pij: matrix (m+n downto 0, m+n downto 0);

	begin
		--Transferencia dos valores de arg_Rv para Lv e Rv, respectivamente:
		transf_a: for i in arg_Lv'range loop
			a(i) := arg_Lv(i);
		end loop;
		transf_b: for i in arg_Rv'range loop
			b(i) := arg_Rv(i);
		end loop;

		--Extensao dos bits de sinal em a e b:
		a(m+n-1 downto m) := (others => arg_Lv(arg_Lv'left));	--(others => arg_Lv(arg_Lv'LEFT));		-- blinha(m+n-1 downto n => b('left)); para signed
		b(m+n-1 downto n) := (others => arg_Rv(arg_Rv'left));	--(others => arg_Rv(arg_Rv'LEFT));		-- alinha(m+n-1 downto m => a('left)); para signed

		--Inicializamos as matrizes de interconexao Cij e Pij:
		--Cij(i, 0) = 0
		initCij: for i in 0 to m+n-1 loop			-- for i in m+n-1 downto 0 loop para signed
			Cij(i, 0) := '0';
		end loop initCij;

		--Pij(i, 0) = 0
		initPij1: for i in 0 to m+n loop			-- for i in m+n downto 0 loop para signed / P(0,0) useless
			Pij(i, 0) := '0';
		end loop initPij1;

		--Pij(m, i) = 0
		initPij2: for i in 1 to m+n-1 loop
			Pij(m, i) := '0';
		end loop initPij2;

		--Para inicializar a matriz de interconexao Mij eh necessario utilizar lacos de iteracao:
		--Mij(i, j) = A(i)B(j)
		Mijrow: for j in 0 to m+n-1 loop
			Mijcol: for i in 0 to m+n-1 loop
				Mij(i,j) := a(i) and b(j);
			end loop Mijcol;
		end loop Mijrow;

		--Finalmente, podemos interligar os modulos de processamento.
		--Pi,j	Pij(i, j) 	0 <= i <= m, 0 <= j <= m+n
		Pijrow: for j in 0 to m+n-1 loop
			Pijcol: for i in 0 to m+n-1 loop
				Pij(i,j+1) := Pij(i+1,j) xor Mij(i,j) xor Cij(i,j);
				Cij(i,j+1) := (Pij(i+1,j) and (Mij(i,j) or Cij(i,j))) or (Mij(i,j) and Cij(i,j));
			end loop Pijcol;
		end loop Pijrow;

		--O resultado final p sera igual a:
		--p(i) = Pij(0, i+1)		0 <= i <= m+n-1
		initPi: for i in 0 to m+n-1 loop
			p(i) := Pij(0,i+1);
		end loop initPi;
			
		--RESULT(i) = p(0, i+1)		i in (p'range)
		genR: for i in RESULT'range loop
			RESULT(i) := p(i-2*RESULT'right);
		end loop genR;

		return RESULT;
	end function;

-- funcoes EXTERNAS

	function to_real (arg_L: fixed) return real IS
		variable s : real := 0.0;
		variable aux: fixed(arg_L'left DOWNTO arg_L'right);
	BEGIN
	  aux := arg_L;
		IF (arg_L(arg_L'left) = '1') THEN
			s := s - 2.0**(arg_L'left);
		END IF;
		FOR i IN aux'left - 1 DOWNTO aux'right LOOP
			IF(aux(i) = '1') THEN
				s := s + (2.0**i);
			END IF;
		END LOOP;
		RETURN s;
	END to_real;

	function to_fixed (arg_L: real; max_range, min_range: fixed_range) return fixed IS 
		variable s : fixed(max_range DOWNTO min_range);
		variable aux : real := 0.0;
		variable absL : real;
	BEGIN
		IF (arg_L < 0.0) THEN
			aux := aux - 2.0**(max_range);
			s(max_range) := '1';
			
		ELSE 
			s(max_range) := '0';
			
		END IF;
		absL := abs(arg_L);
		FOR i IN max_range-1 DOWNTO min_range LOOP
			IF(aux + 2.0**i <= absL) THEN
				s(i) := '1';
				aux := aux + 2.0**i;
			ELSE
				s(i) := '0';
			END IF;
		END LOOP;

		RETURN s;
	END to_fixed;


	function to_fixed (arg_L: integer; max_range: fixed_range := MAX_IND; min_range: fixed_range := 0) return fixed IS
	 	variable s : fixed(min_range TO max_range);
	 	variable aux : integer := 0;
	 	variable absL : integer;
	BEGIN
	  	absL := abs(arg_L);
	  	FOR i IN max_range DOWNTO min_range LOOP
			IF (i < 0) THEN
			  s(i) := '0';
			ELSIF (aux + 2**i <= absL) THEN
				s(i) := '1';
				aux := aux + 2**i;
			ELSE
				s(i) := '0';
			END IF;
		END LOOP;	
		IF(arg_L >= 0) THEN
			RETURN s;
		ELSE
			RETURN COMP1_FIXED(s) + 1;
		END IF;
	END to_fixed;


	function to_integer (arg_L: fixed) return integer IS
	 	variable s : INTEGER := 0;
	 	variable aux: fixed(arg_L'low TO arg_L'high);
	BEGIN
	  aux := arg_L;
	  IF(arg_L(arg_L'high) >= '1') THEN
			aux := COMP1_FIXED(arg_L - 1);
		END IF;
	  	abc: FOR i IN 0 to aux'high LOOP
			IF(aux(i) = '1') THEN
				s := s + (2**i);
			END IF;
		END LOOP abc;
		IF(arg_L(arg_L'high) >= '1') THEN -- numero negativo
		  IF(arg_L(-1) = '0') THEN -- aproximacao
		    s := s + 1;
		  END IF;
		  RETURN -s;
		ELSE -- numero positivo
		  IF(arg_L(-1) = '1') THEN -- aproximacao
		    s := s + 1;
		  END IF;
			RETURN s;
		END IF;
	END to_integer;


	function "+"(arg_L, arg_R: fixed) return fixed IS
	 	constant arg_L_L : INTEGER := arg_L'left;
		constant arg_L_R : INTEGER := arg_L'right;
		constant arg_R_L : INTEGER := arg_R'left;
		constant arg_R_R : INTEGER := arg_R'right;
		constant resultado_L : INTEGER := Max(arg_L'left, arg_R'left);
		constant resultado_R : INTEGER := Max(arg_L'right, arg_R'right);

	 	variable L01 : fixed(resultado_L downto resultado_R) := (others => '0');
	 	variable R01 : fixed(resultado_L downto resultado_R) := (others => '0');

	BEGIN

		L01(arg_L_L downto resultado_R) := arg_L(arg_L_L downto resultado_R);
		R01(arg_R_L downto resultado_R) := arg_R(arg_R_L downto resultado_R);

		L01(resultado_L downto arg_L_L) := (others => arg_L(arg_L_L));
		R01(resultado_L downto arg_R_L) := (others => arg_L(arg_L_L));
		
		return ADD_SUB_FIXED(L01, R01, '0');
	END "+";

	function "-"(arg_L, arg_R: fixed) return fixed IS
	 	constant arg_L_L : INTEGER := arg_L'left;
		constant arg_L_R : INTEGER := arg_L'right;
		constant arg_R_L : INTEGER := arg_R'left;
		constant arg_R_R : INTEGER := arg_R'right;
		constant resultado_L : INTEGER := Max(arg_L'left, arg_R'left);
		constant resultado_R : INTEGER := Max(arg_L'right, arg_R'right);

	 	variable L01 : fixed(resultado_L downto resultado_R) := (others => '0');
	 	variable R01 : fixed(resultado_L downto resultado_R) := (others => '0');

	BEGIN

		L01(arg_L_L downto resultado_R) := arg_L(arg_L_L downto resultado_R);
		R01(arg_R_L downto resultado_R) := arg_R(arg_R_L downto resultado_R);

		L01(resultado_L downto arg_L_L) := (others => arg_L(arg_L_L));
		R01(resultado_L downto arg_R_L) := (others => arg_L(arg_L_L));
		
		return ADD_SUB_FIXED(L01, COMP1_FIXED(R01), '1');
	END "-";


	function "+"(arg_L: fixed; arg_R: INTEGER) return fixed IS
	 	variable s : fixed(arg_L'range);
	BEGIN
	  	s:= to_fixed(arg_R, arg_L'high, arg_L'low);
	  	return arg_L + s;
	END "+";


	function "+"(arg_L: INTEGER; arg_R: fixed) return fixed IS
	 	variable s : fixed(arg_R'range);
	BEGIN
	  	s:= to_fixed(arg_L, arg_R'high, arg_R'low);
	  	return s + arg_R;
	END "+";


	function "-"(arg_L: fixed; arg_R: INTEGER) return fixed IS
	 	variable s : fixed(arg_L'range);
	BEGIN
	  	s:= to_fixed(arg_R, arg_L'high, arg_L'low);
	  	return arg_L - s;
	END "-";


	function "-"(arg_L: INTEGER; arg_R: fixed) return fixed IS
	 	variable s : fixed(arg_R'range);
	BEGIN
	  	s:= to_fixed(arg_L, arg_R'high, arg_R'low);
	  	return s - arg_R;
	END "-";

	function "+"(arg_L: fixed; arg_R: real) return fixed IS 
		variable s : fixed(arg_L'range);
	BEGIN
	  	s:= to_fixed(arg_R, arg_L'high, arg_L'low);
	  	return arg_L + s;
	END "+";

	function "+"(arg_L: real; arg_R: fixed) return fixed IS 
		variable s : fixed(arg_R'range);
	BEGIN
	  	s:= to_fixed(arg_L, arg_R'high, arg_R'low);
	  	return s + arg_R;
	END "+";


	function "-"(arg_L: fixed; arg_R: real) return fixed IS 
		variable s : fixed(arg_L'range);
	BEGIN
	  	s:= to_fixed(arg_R, arg_L'high, arg_L'low);
	  	return arg_L - s;
	END "-";

	function "-"(arg_L: real; arg_R: fixed) return fixed IS 
		variable s : fixed(arg_R'range);
	BEGIN
	  	s:= to_fixed(arg_L, arg_R'high, arg_R'low);
	  	return s - arg_R;
	END "-";

	function "*"(arg_L, arg_R: fixed) return fixed IS
		constant arg_L_L : INTEGER := arg_L'left;
		constant arg_L_R : INTEGER := arg_L'right;
		constant arg_R_L : INTEGER := arg_R'left;
		constant arg_R_R : INTEGER := arg_R'right;
		constant resultado_L : INTEGER := Max(arg_L'left, arg_R'left);
		constant resultado_R : INTEGER := Max(arg_L'right, arg_R'right);

	 	variable L01 : fixed(resultado_L downto resultado_R) := (others => '0');
	 	variable R01 : fixed(resultado_L downto resultado_R) := (others => '0');

	BEGIN

		L01(arg_L_L downto resultado_R) := arg_L(arg_L_L downto resultado_R);
		R01(arg_R_L downto resultado_R) := arg_R(arg_R_L downto resultado_R);

		L01(resultado_L downto arg_L_L) := (others => arg_L(arg_L_L));
		R01(resultado_L downto arg_R_L) := (others => arg_L(arg_L_L));
		
		return MULT_FIXED(L01, R01);
	END "*";

	function "*"(arg_L: fixed; arg_R: real) return fixed IS 
		variable s : fixed(arg_L'range);
	BEGIN
	  	s:= to_fixed(arg_R, arg_L'high, arg_L'low);
	  	return arg_L * s;
	END "*";

	function "*"(arg_L: real; arg_R: fixed) return fixed IS
		variable s : fixed(arg_R'range);
	BEGIN
	  	s:= to_fixed(arg_L, arg_R'high, arg_R'low);
	  	return s * arg_R;
	END "*";

	function "*"(arg_L: fixed; arg_R: INTEGER) return fixed IS
	 	variable s : fixed(arg_L'range);
	BEGIN
	  	s:= to_fixed(arg_R, arg_L'high, arg_L'low);
	  	return arg_L * s;
	END "*";


	function "*"(arg_L: INTEGER; arg_R: fixed) return fixed IS
	 	variable s : fixed(arg_R'range);
	BEGIN
	  	s:= to_fixed(arg_L, arg_R'high, arg_R'low);
	  	return s * arg_R;
	END "*";

END PACKAGE BODY fixed_package;