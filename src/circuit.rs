use bellperson::{
    gadgets::{boolean::AllocatedBit, num::AllocatedNum},
    ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use nova_snark::traits::circuit::StepCircuit;

#[derive(Clone, Debug, Default)]
pub struct ProximityCircuit<F: PrimeField + PrimeFieldBits> {
    x: F,
    y: F,
}

impl<F: PrimeField + PrimeFieldBits> ProximityCircuit<F> {
    pub fn new(x: F, y: F) -> Self {
        Self { x, y }
    }
}

impl<F> StepCircuit<F> for ProximityCircuit<F>
where
    F: PrimeField + PrimeFieldBits,
{
    fn arity(&self) -> usize {
        1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let x_ref = F::from(5000);
        let y_ref = F::from(5000);
        let radius = F::from(100);
        // the number of bits required to represent any number used: it is 2n + 1 where n is the number of bits required to represent the largest number
        // because we then compare the difference of the sum of squares with the square of the radius
        let num_bits = 13 * 2 + 1;

        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(self.x))?;
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(self.y))?;

        // check greater of x and x_ref to perform the subtraction
        let x_lt = less_than(&x, x_ref, num_bits, &mut cs.namespace(|| "x lt x_ref"))?;
        let y_lt = less_than(&y, y_ref, num_bits, &mut cs.namespace(|| "y lt y_ref"))?;

        // Calculate diff
        let x_diff = AllocatedNum::alloc(cs.namespace(|| "x_diff"), || {
            let x_value = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            if x_lt.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                Ok(x_ref - x_value)
            } else {
                Ok(x_value - x_ref)
            }
        })?;

        let y_diff = AllocatedNum::alloc(cs.namespace(|| "y_diff"), || {
            let y_value = y.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            if y_lt.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                Ok(y_ref - y_value)
            } else {
                Ok(y_value - y_ref)
            }
        })?;

        // Enforce diff calculation
        // ???

        // Check if point is within radius (x_diff^2 + y_diff^2 <= radius^2)
        // calculate x_diff^2 and y_diff^2
        let x_diff_squared = AllocatedNum::alloc(cs.namespace(|| "x_diff_squared"), || {
            let x_diff_value = x_diff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(x_diff_value * x_diff_value)
        })?;

        let y_diff_squared = AllocatedNum::alloc(cs.namespace(|| "y_diff_squared"), || {
            let y_diff_value = y_diff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(y_diff_value * y_diff_value)
        })?;

        cs.enforce(
            || "enforce x_diff_squared",
            |lc| lc + x_diff.get_variable(),
            |lc| lc + x_diff.get_variable(),
            |lc| lc + x_diff_squared.get_variable(),
        );

        cs.enforce(
            || "enforce y_diff_squared",
            |lc| lc + y_diff.get_variable(),
            |lc| lc + y_diff.get_variable(),
            |lc| lc + y_diff_squared.get_variable(),
        );

        let sum_squared = AllocatedNum::alloc(cs.namespace(|| "sum_squared"), || {
            let x_diff_squared_value = x_diff_squared
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let y_diff_squared_value = y_diff_squared
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(x_diff_squared_value + y_diff_squared_value)
        })?;

        cs.enforce(
            || "enforce sum_squared",
            |lc| lc + x_diff_squared.get_variable() + y_diff_squared.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + sum_squared.get_variable(),
        );

        let radius_squared = radius * radius;

        let is_within_radius = less_than(
            &sum_squared,
            radius_squared,
            num_bits,
            &mut cs.namespace(|| "x_sq + y_sq lt r_sq"),
        )?;

        let output = AllocatedNum::alloc(cs.namespace(|| "output"), || {
            let is_within_radius_value = is_within_radius
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(if is_within_radius_value {
                F::from(1)
            } else {
                F::from(0)
            })
        })?;

        Ok(vec![output])
    }

    fn output(&self, _z: &[F]) -> Vec<F> {
        vec![F::from(1)]
    }
}

fn num_to_bits_le_bounded<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    n: AllocatedNum<F>,
    num_bits: u8,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let opt_bits = match n.get_value() {
        Some(v) => v
            .to_le_bits()
            .into_iter()
            .take(num_bits as usize)
            .map(Some)
            .collect::<Vec<Option<bool>>>(),
        None => vec![None; num_bits as usize],
    };

    // Add one witness per input bit in little-endian bit order
    let bits_circuit = opt_bits
        .into_iter()
        .enumerate()
        // AllocateBit enforces the value to be 0 or 1 at the constraint level
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("b_{}", i)), b).unwrap())
        .collect::<Vec<AllocatedBit>>();

    let mut weighted_sum_lc = LinearCombination::zero();
    let mut pow2 = F::ONE;

    for bit in bits_circuit.iter() {
        weighted_sum_lc = weighted_sum_lc + (pow2, bit.get_variable());
        pow2 = pow2.double();
    }

    cs.enforce(
        || "bit decomposition check",
        |lc| lc + &weighted_sum_lc,
        |lc| lc + CS::one(),
        |lc| lc + n.get_variable(),
    );

    Ok(bits_circuit)
}

/* fn get_msb_index<F: PrimeField + PrimeFieldBits>(n: F) -> u8 {
    n.to_le_bits()
        .into_iter()
        .enumerate()
        .rev()
        .find(|(_, b)| *b)
        .unwrap()
        .0 as u8
} */

fn less_than<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    a: &AllocatedNum<F>,
    b: F,
    num_bits: u8,
    cs: &mut CS,
) -> Result<AllocatedBit, SynthesisError> {
    let shifted_diff = AllocatedNum::alloc(cs.namespace(|| "shifted_diff"), || {
        let a_value = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        Ok(a_value + F::from(1 << num_bits) - b)
    })?;

    cs.enforce(
        || "shifted_diff_computation",
        |lc| lc + a.get_variable() + (F::from(1 << num_bits) - b, CS::one()),
        |lc: LinearCombination<F>| lc + CS::one(),
        |lc| lc + shifted_diff.get_variable(),
    );

    let shifted_diff_bits = num_to_bits_le_bounded::<F, CS>(cs, shifted_diff, num_bits + 1)?;

    let output = AllocatedBit::alloc(cs.namespace(|| "output"), {
        Some(
            !shifted_diff_bits[num_bits as usize]
                .get_value()
                .unwrap_or(false),
        )
    })?;

    // would like to enforce shifted_diff_bits[num_bits as usize] == (1 - output), to ensure output is opposite of the MSB
    /*     cs.enforce(
        || "output_computation",
        |lc| lc + shifted_diff_bits[num_bits as usize].get_variable(),
        |lc: LinearCombination<F>| lc + CS::one(),
        |lc| lc + (F::ONE - output.get_variable(), CS::one()),
    ); */

    Ok(output)
}

#[cfg(test)]
mod tests {
    use crate::circuit::ProximityCircuit;
    use ff::Field;
    use nova_snark::traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    };
    use nova_snark::{provider, spartan};
    use nova_snark::{CompressedSNARK, PublicParams, RecursiveSNARK};
    #[test]
    fn test_all() {
        let generate_keys_to_json = true;

        type G1 = pasta_curves::pallas::Point;
        type G2 = pasta_curves::vesta::Point;

        type EE1<G1> = provider::ipa_pc::EvaluationEngine<G1>;
        type EE2<G2> = provider::ipa_pc::EvaluationEngine<G2>;

        type S1Prime<G1> = spartan::ppsnark::RelaxedR1CSSNARK<G1, EE1<G1>>;
        type S2Prime<G2> = spartan::ppsnark::RelaxedR1CSSNARK<G2, EE2<G2>>;

        let circuit_primary = TrivialTestCircuit::default();
        let circuit_secondary = ProximityCircuit {
            x: <G2 as Group>::Scalar::from(5001u64),
            y: <G2 as Group>::Scalar::from(5001u64),
        };

        // produce public parameters
        let pp = PublicParams::<
            G1,
            G2,
            TrivialTestCircuit<<G1 as Group>::Scalar>,
            ProximityCircuit<<G2 as Group>::Scalar>,
        >::setup(circuit_primary.clone(), circuit_secondary.clone());

        let num_steps = 1;

        // produce a recursive SNARK
        let mut recursive_snark = RecursiveSNARK::<
            G1,
            G2,
            TrivialTestCircuit<<G1 as Group>::Scalar>,
            ProximityCircuit<<G2 as Group>::Scalar>,
        >::new(
            &pp,
            &circuit_primary,
            &circuit_secondary,
            vec![<G1 as Group>::Scalar::ONE],
            vec![<G2 as Group>::Scalar::ZERO],
        );

        for _i in 0..num_steps {
            let res = recursive_snark.prove_step(
                &pp,
                &circuit_primary,
                &circuit_secondary,
                vec![<G1 as Group>::Scalar::ONE],
                vec![<G2 as Group>::Scalar::ZERO],
            );
            assert!(res.is_ok());
        }

        // verify the recursive SNARK
        let res = recursive_snark.verify(
            &pp,
            num_steps,
            &[<G1 as Group>::Scalar::ONE],
            &[<G2 as Group>::Scalar::ZERO],
        );
        assert!(res.is_ok());

        let (zn_primary, zn_secondary) = res.unwrap();

        // sanity: check the claimed output with a direct computation of the same
        assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::ONE]);
        let mut zn_secondary_direct = vec![<G2 as Group>::Scalar::ZERO];
        for _i in 0..num_steps {
            zn_secondary_direct = circuit_secondary.clone().output(&zn_secondary_direct);
        }
        assert_eq!(zn_secondary, zn_secondary_direct);
        assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(1)]);

        // produce the prover and verifier keys for compressed snark
        let (pk, vk) = CompressedSNARK::<_, _, _, _, S1Prime<G1>, S2Prime<G2>>::setup(&pp).unwrap();

        if generate_keys_to_json {
            let serialized_vk = serde_json::to_string(&vk).unwrap();
            std::fs::write(std::path::Path::new("vk.json"), serialized_vk)
                .expect("Unable to write file");
        }
        // produce a compressed SNARK
        let res = CompressedSNARK::<_, _, _, _, S1Prime<G1>, S2Prime<G2>>::prove(
            &pp,
            &pk,
            &recursive_snark,
        );
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        if generate_keys_to_json {
            let serialized_compressed_snark = serde_json::to_string(&compressed_snark).unwrap();
            std::fs::write(
                std::path::Path::new("compressed-snark.json"),
                serialized_compressed_snark,
            )
            .expect("Unable to write file");
        }
        // verify the compressed SNARK
        let res = compressed_snark.verify(
            &vk,
            num_steps,
            vec![<G1 as Group>::Scalar::ONE],
            vec![<G2 as Group>::Scalar::ZERO],
        );
        assert!(res.is_ok());
    }
}
