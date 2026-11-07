from pathlib import Path
import sys,json,hashlib,math
root=Path.cwd().resolve()
def deny(event,args):
    if event in ('subprocess.Popen','socket.connect','socket.getaddrinfo'):
        raise RuntimeError('Bounded canonical arithmetic probe forbids native/network/process calls')
sys.addaudithook(deny)
import src.core.constants as c
import src.core.formulas as f
import src.core.transonic_background as tb
import scripts.gen_d1_hierarchy_table as gh
origins={m.__name__:str(Path(m.__file__).resolve()) for m in [c,f,tb,gh]}
assert all(Path(p).is_relative_to(root) for p in origins.values())
hier=gh.compute_bec_hierarchy()
p=tb.heidelberg_K39();bg=tb.solve_transonic_background(p);k=bg.surface_gravity
rows=[]
for factor in [1.,2.]:
    kk=factor*k
    transport=f.beliaev_transport_coefficients(p.density_upstream,p.scattering_length,kk,p.sound_speed_upstream,p.healing_length)
    rows.append({'kappa_factor':factor,'kappa':kk,'Gamma_Bel':float(transport['Gamma_Bel']),'delta_diss':float(f.first_order_correction(transport['Gamma_Bel'],kk)),'delta_disp':float(f.kappa_scaling_dispersive(kk,p.healing_length,p.sound_speed_upstream)),'gamma_1':float(transport['gamma_1']),'gamma_2':float(transport['gamma_2'])})
ratios={key:rows[1][key]/rows[0][key] for key in ['Gamma_Bel','delta_diss','delta_disp','gamma_1','gamma_2']}
assert math.isclose(ratios['Gamma_Bel'],4.) and math.isclose(ratios['delta_diss'],2.) and math.isclose(ratios['delta_disp'],4.)
g=c.GRAPHENE_PLATFORMS['Dean_bilayer_nozzle'];derived_T=float(f.hawking_temperature(g['gradient_s1']))
r={'scope':'Existing canonical producer arithmetic at adopted parameters only; no new physical damping/graphene response derivation, no scientific source mutation.','origins':origins,'source_hashes':{str(Path(v).relative_to(root)):hashlib.sha256(Path(v).read_bytes()).hexdigest() for v in origins.values()},'actual_bec_hierarchy':hier,'fixed_material_kappa_sweep':{'inputs':{'density_1D':p.density_upstream,'a_s':p.scattering_length,'c_s':p.sound_speed_upstream,'xi':p.healing_length},'rows':rows,'doubling_ratios':ratios,'diss_to_disp_ratio_changes_by':ratios['delta_diss']/ratios['delta_disp']},'graphene_operating_point':{'adopted_gradient':g['gradient_s1'],'T_H_registry_rounded_K':g['T_H_K'],'T_H_from_canonical_gradient_K':derived_T,'omega_from_rounded_temperature':c.K_B*g['T_H_K']/c.HBAR,'omega_from_unrounded_canonical_temperature':c.K_B*derived_T/c.HBAR,'geometry_gradient_estimate':g['c_s']/(g['nozzle_throat_nm']*1e-9),'scope':'Registry gradient and c_s/L geometry estimate are distinct adopted/approximate inputs; do not silently select new physical parameters.'}}
print(json.dumps(r,indent=2,default=lambda x:float(x)))
