(set-logic HORN)
(declare-datatypes ((Nat_0 0)) (((Z_13 ) (Z_14 (unS_0 Nat_0)))))
(declare-fun diseqNat_0 (Nat_0 Nat_0) Bool)
(declare-fun unS_1 (Nat_0 Nat_0) Bool)
(declare-fun isZ_2 (Nat_0) Bool)
(declare-fun isZ_3 (Nat_0) Bool)
(assert (forall ((x_169 Nat_0))
	(unS_1 x_169 (Z_14 x_169))))
(assert (isZ_2 Z_13))
(assert (forall ((x_171 Nat_0))
	(isZ_3 (Z_14 x_171))))
(assert (forall ((x_172 Nat_0))
	(diseqNat_0 Z_13 (Z_14 x_172))))
(assert (forall ((x_173 Nat_0))
	(diseqNat_0 (Z_14 x_173) Z_13)))
(assert (forall ((x_174 Nat_0) (x_175 Nat_0))
	(=> (diseqNat_0 x_174 x_175)
	    (diseqNat_0 (Z_14 x_174) (Z_14 x_175)))))
(declare-fun add_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun minus_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun le_0 (Nat_0 Nat_0) Bool)
(declare-fun ge_0 (Nat_0 Nat_0) Bool)
(declare-fun lt_0 (Nat_0 Nat_0) Bool)
(declare-fun gt_0 (Nat_0 Nat_0) Bool)
(declare-fun mult_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun div_0 (Nat_0 Nat_0 Nat_0) Bool)
(declare-fun mod_0 (Nat_0 Nat_0 Nat_0) Bool)
(assert (forall ((y_21 Nat_0))
	(add_0 y_21 Z_13 y_21)))
(assert (forall ((r_1 Nat_0) (x_163 Nat_0) (y_21 Nat_0))
	(=> (add_0 r_1 x_163 y_21)
	    (add_0 (Z_14 r_1) (Z_14 x_163) y_21))))
(assert (forall ((y_21 Nat_0))
	(minus_0 Z_13 Z_13 y_21)))
(assert (forall ((r_1 Nat_0) (x_163 Nat_0) (y_21 Nat_0))
	(=> (minus_0 r_1 x_163 y_21)
	    (minus_0 (Z_14 r_1) (Z_14 x_163) y_21))))
(assert (forall ((y_21 Nat_0))
	(le_0 Z_13 y_21)))
(assert (forall ((x_163 Nat_0) (y_21 Nat_0))
	(=> (le_0 x_163 y_21)
	    (le_0 (Z_14 x_163) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(ge_0 y_21 Z_13)))
(assert (forall ((x_163 Nat_0) (y_21 Nat_0))
	(=> (ge_0 x_163 y_21)
	    (ge_0 (Z_14 x_163) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(lt_0 Z_13 (Z_14 y_21))))
(assert (forall ((x_163 Nat_0) (y_21 Nat_0))
	(=> (lt_0 x_163 y_21)
	    (lt_0 (Z_14 x_163) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(gt_0 (Z_14 y_21) Z_13)))
(assert (forall ((x_163 Nat_0) (y_21 Nat_0))
	(=> (gt_0 x_163 y_21)
	    (gt_0 (Z_14 x_163) (Z_14 y_21)))))
(assert (forall ((y_21 Nat_0))
	(mult_0 Z_13 Z_13 y_21)))
(assert (forall ((r_1 Nat_0) (x_163 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (mult_0 r_1 x_163 y_21)
			(add_0 z_15 r_1 y_21))
		(mult_0 z_15 (Z_14 x_163) y_21))))
(assert (forall ((x_163 Nat_0) (y_21 Nat_0))
	(=> (lt_0 x_163 y_21)
	    (div_0 Z_13 x_163 y_21))))
(assert (forall ((r_1 Nat_0) (x_163 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (ge_0 x_163 y_21)
			(minus_0 z_15 x_163 y_21)
			(div_0 r_1 z_15 y_21))
		(div_0 (Z_14 r_1) x_163 y_21))))
(assert (forall ((x_163 Nat_0) (y_21 Nat_0))
	(=> (lt_0 x_163 y_21)
	    (mod_0 x_163 x_163 y_21))))
(assert (forall ((r_1 Nat_0) (x_163 Nat_0) (y_21 Nat_0) (z_15 Nat_0))
	(=>	(and (ge_0 x_163 y_21)
			(minus_0 z_15 x_163 y_21)
			(mod_0 r_1 z_15 y_21))
		(mod_0 r_1 x_163 y_21))))
(declare-datatypes ((pair_0 0)) (((pair_1 (projpair_0 Nat_0) (projpair_1 Nat_0)))))
(declare-fun diseqpair_0 (pair_0 pair_0) Bool)
(declare-fun projpair_4 (Nat_0 pair_0) Bool)
(declare-fun projpair_5 (Nat_0 pair_0) Bool)
(declare-fun ispair_0 (pair_0) Bool)
(assert (forall ((x_176 Nat_0) (x_177 Nat_0))
	(projpair_4 x_176 (pair_1 x_176 x_177))))
(assert (forall ((x_176 Nat_0) (x_177 Nat_0))
	(projpair_5 x_177 (pair_1 x_176 x_177))))
(assert (forall ((x_179 Nat_0) (x_180 Nat_0))
	(ispair_0 (pair_1 x_179 x_180))))
(assert (forall ((x_181 Nat_0) (x_182 Nat_0) (x_183 Nat_0) (x_184 Nat_0))
	(=> (diseqNat_0 x_181 x_183)
	    (diseqpair_0 (pair_1 x_181 x_182) (pair_1 x_183 x_184)))))
(assert (forall ((x_181 Nat_0) (x_182 Nat_0) (x_183 Nat_0) (x_184 Nat_0))
	(=> (diseqNat_0 x_182 x_184)
	    (diseqpair_0 (pair_1 x_181 x_182) (pair_1 x_183 x_184)))))
(declare-datatypes ((list_0 0)) (((nil_0 ) (cons_0 (head_0 Nat_0) (tail_0 list_0)))))
(declare-fun diseqlist_0 (list_0 list_0) Bool)
(declare-fun head_1 (Nat_0 list_0) Bool)
(declare-fun tail_2 (list_0 list_0) Bool)
(declare-fun isnil_0 (list_0) Bool)
(declare-fun iscons_0 (list_0) Bool)
(assert (forall ((x_186 Nat_0) (x_187 list_0))
	(head_1 x_186 (cons_0 x_186 x_187))))
(assert (forall ((x_186 Nat_0) (x_187 list_0))
	(tail_2 x_187 (cons_0 x_186 x_187))))
(assert (isnil_0 nil_0))
(assert (forall ((x_189 Nat_0) (x_190 list_0))
	(iscons_0 (cons_0 x_189 x_190))))
(assert (forall ((x_191 Nat_0) (x_192 list_0))
	(diseqlist_0 nil_0 (cons_0 x_191 x_192))))
(assert (forall ((x_193 Nat_0) (x_194 list_0))
	(diseqlist_0 (cons_0 x_193 x_194) nil_0)))
(assert (forall ((x_195 Nat_0) (x_196 list_0) (x_197 Nat_0) (x_198 list_0))
	(=> (diseqNat_0 x_195 x_197)
	    (diseqlist_0 (cons_0 x_195 x_196) (cons_0 x_197 x_198)))))
(assert (forall ((x_195 Nat_0) (x_196 list_0) (x_197 Nat_0) (x_198 list_0))
	(=> (diseqlist_0 x_196 x_198)
	    (diseqlist_0 (cons_0 x_195 x_196) (cons_0 x_197 x_198)))))
(declare-datatypes ((pair_2 0)) (((pair_3 (projpair_2 list_0) (projpair_3 list_0)))))
(declare-fun diseqpair_1 (pair_2 pair_2) Bool)
(declare-fun projpair_6 (list_0 pair_2) Bool)
(declare-fun projpair_7 (list_0 pair_2) Bool)
(declare-fun ispair_1 (pair_2) Bool)
(assert (forall ((x_199 list_0) (x_200 list_0))
	(projpair_6 x_199 (pair_3 x_199 x_200))))
(assert (forall ((x_199 list_0) (x_200 list_0))
	(projpair_7 x_200 (pair_3 x_199 x_200))))
(assert (forall ((x_202 list_0) (x_203 list_0))
	(ispair_1 (pair_3 x_202 x_203))))
(assert (forall ((x_204 list_0) (x_205 list_0) (x_206 list_0) (x_207 list_0))
	(=> (diseqlist_0 x_204 x_206)
	    (diseqpair_1 (pair_3 x_204 x_205) (pair_3 x_206 x_207)))))
(assert (forall ((x_204 list_0) (x_205 list_0) (x_206 list_0) (x_207 list_0))
	(=> (diseqlist_0 x_205 x_207)
	    (diseqpair_1 (pair_3 x_204 x_205) (pair_3 x_206 x_207)))))
(declare-datatypes ((Q_0 0)) (((Q_1 (projQ_0 list_0) (projQ_1 list_0)))))
(declare-fun diseqQ_0 (Q_0 Q_0) Bool)
(declare-fun projQ_2 (list_0 Q_0) Bool)
(declare-fun projQ_3 (list_0 Q_0) Bool)
(declare-fun isQ_0 (Q_0) Bool)
(assert (forall ((x_208 list_0) (x_209 list_0))
	(projQ_2 x_208 (Q_1 x_208 x_209))))
(assert (forall ((x_208 list_0) (x_209 list_0))
	(projQ_3 x_209 (Q_1 x_208 x_209))))
(assert (forall ((x_211 list_0) (x_212 list_0))
	(isQ_0 (Q_1 x_211 x_212))))
(assert (forall ((x_213 list_0) (x_214 list_0) (x_215 list_0) (x_216 list_0))
	(=> (diseqlist_0 x_213 x_215)
	    (diseqQ_0 (Q_1 x_213 x_214) (Q_1 x_215 x_216)))))
(assert (forall ((x_213 list_0) (x_214 list_0) (x_215 list_0) (x_216 list_0))
	(=> (diseqlist_0 x_214 x_216)
	    (diseqQ_0 (Q_1 x_213 x_214) (Q_1 x_215 x_216)))))
(declare-datatypes ((Maybe_0 0)) (((Nothing_0 ) (Just_0 (projJust_0 Nat_0)))))
(declare-fun diseqMaybe_0 (Maybe_0 Maybe_0) Bool)
(declare-fun projJust_2 (Nat_0 Maybe_0) Bool)
(declare-fun isNothing_0 (Maybe_0) Bool)
(declare-fun isJust_0 (Maybe_0) Bool)
(assert (forall ((x_218 Nat_0))
	(projJust_2 x_218 (Just_0 x_218))))
(assert (isNothing_0 Nothing_0))
(assert (forall ((x_220 Nat_0))
	(isJust_0 (Just_0 x_220))))
(assert (forall ((x_221 Nat_0))
	(diseqMaybe_0 Nothing_0 (Just_0 x_221))))
(assert (forall ((x_222 Nat_0))
	(diseqMaybe_0 (Just_0 x_222) Nothing_0)))
(assert (forall ((x_223 Nat_0) (x_224 Nat_0))
	(=> (diseqNat_0 x_223 x_224)
	    (diseqMaybe_0 (Just_0 x_223) (Just_0 x_224)))))
(declare-datatypes ((Maybe_1 0)) (((Nothing_1 ) (Just_1 (projJust_1 Q_0)))))
(declare-fun diseqMaybe_1 (Maybe_1 Maybe_1) Bool)
(declare-fun projJust_3 (Q_0 Maybe_1) Bool)
(declare-fun isNothing_1 (Maybe_1) Bool)
(declare-fun isJust_1 (Maybe_1) Bool)
(assert (forall ((x_226 Q_0))
	(projJust_3 x_226 (Just_1 x_226))))
(assert (isNothing_1 Nothing_1))
(assert (forall ((x_228 Q_0))
	(isJust_1 (Just_1 x_228))))
(assert (forall ((x_229 Q_0))
	(diseqMaybe_1 Nothing_1 (Just_1 x_229))))
(assert (forall ((x_230 Q_0))
	(diseqMaybe_1 (Just_1 x_230) Nothing_1)))
(assert (forall ((x_231 Q_0) (x_232 Q_0))
	(=> (diseqQ_0 x_231 x_232)
	    (diseqMaybe_1 (Just_1 x_231) (Just_1 x_232)))))
(declare-datatypes ((E_0 0)) (((Empty_0 ) (EnqL_0 (projEnqL_0 Nat_0) (projEnqL_1 E_0)) (EnqR_0 (projEnqR_0 E_0) (projEnqR_1 Nat_0)) (DeqL_0 (projDeqL_0 E_0)) (DeqR_0 (projDeqR_0 E_0)) (App_0 (projApp_0 E_0) (projApp_1 E_0)))))
(declare-fun diseqE_0 (E_0 E_0) Bool)
(declare-fun projEnqL_2 (Nat_0 E_0) Bool)
(declare-fun projEnqL_3 (E_0 E_0) Bool)
(declare-fun projEnqR_2 (E_0 E_0) Bool)
(declare-fun projEnqR_3 (Nat_0 E_0) Bool)
(declare-fun projDeqL_1 (E_0 E_0) Bool)
(declare-fun projDeqR_1 (E_0 E_0) Bool)
(declare-fun projApp_2 (E_0 E_0) Bool)
(declare-fun projApp_3 (E_0 E_0) Bool)
(declare-fun isEmpty_0 (E_0) Bool)
(declare-fun isEnqL_0 (E_0) Bool)
(declare-fun isEnqR_0 (E_0) Bool)
(declare-fun isDeqL_0 (E_0) Bool)
(declare-fun isDeqR_0 (E_0) Bool)
(declare-fun isApp_0 (E_0) Bool)
(assert (forall ((x_234 Nat_0) (x_235 E_0))
	(projEnqL_2 x_234 (EnqL_0 x_234 x_235))))
(assert (forall ((x_234 Nat_0) (x_235 E_0))
	(projEnqL_3 x_235 (EnqL_0 x_234 x_235))))
(assert (forall ((x_237 E_0) (x_238 Nat_0))
	(projEnqR_2 x_237 (EnqR_0 x_237 x_238))))
(assert (forall ((x_237 E_0) (x_238 Nat_0))
	(projEnqR_3 x_238 (EnqR_0 x_237 x_238))))
(assert (forall ((x_240 E_0))
	(projDeqL_1 x_240 (DeqL_0 x_240))))
(assert (forall ((x_242 E_0))
	(projDeqR_1 x_242 (DeqR_0 x_242))))
(assert (forall ((x_244 E_0) (x_245 E_0))
	(projApp_2 x_244 (App_0 x_244 x_245))))
(assert (forall ((x_244 E_0) (x_245 E_0))
	(projApp_3 x_245 (App_0 x_244 x_245))))
(assert (isEmpty_0 Empty_0))
(assert (forall ((x_247 Nat_0) (x_248 E_0))
	(isEnqL_0 (EnqL_0 x_247 x_248))))
(assert (forall ((x_249 E_0) (x_250 Nat_0))
	(isEnqR_0 (EnqR_0 x_249 x_250))))
(assert (forall ((x_251 E_0))
	(isDeqL_0 (DeqL_0 x_251))))
(assert (forall ((x_252 E_0))
	(isDeqR_0 (DeqR_0 x_252))))
(assert (forall ((x_253 E_0) (x_254 E_0))
	(isApp_0 (App_0 x_253 x_254))))
(assert (forall ((x_255 Nat_0) (x_256 E_0))
	(diseqE_0 Empty_0 (EnqL_0 x_255 x_256))))
(assert (forall ((x_257 E_0) (x_258 Nat_0))
	(diseqE_0 Empty_0 (EnqR_0 x_257 x_258))))
(assert (forall ((x_259 E_0))
	(diseqE_0 Empty_0 (DeqL_0 x_259))))
(assert (forall ((x_260 E_0))
	(diseqE_0 Empty_0 (DeqR_0 x_260))))
(assert (forall ((x_261 E_0) (x_262 E_0))
	(diseqE_0 Empty_0 (App_0 x_261 x_262))))
(assert (forall ((x_263 Nat_0) (x_264 E_0))
	(diseqE_0 (EnqL_0 x_263 x_264) Empty_0)))
(assert (forall ((x_265 E_0) (x_266 Nat_0))
	(diseqE_0 (EnqR_0 x_265 x_266) Empty_0)))
(assert (forall ((x_267 E_0))
	(diseqE_0 (DeqL_0 x_267) Empty_0)))
(assert (forall ((x_268 E_0))
	(diseqE_0 (DeqR_0 x_268) Empty_0)))
(assert (forall ((x_269 E_0) (x_270 E_0))
	(diseqE_0 (App_0 x_269 x_270) Empty_0)))
(assert (forall ((x_271 Nat_0) (x_272 E_0) (x_273 E_0) (x_274 Nat_0))
	(diseqE_0 (EnqL_0 x_271 x_272) (EnqR_0 x_273 x_274))))
(assert (forall ((x_275 Nat_0) (x_276 E_0) (x_277 E_0))
	(diseqE_0 (EnqL_0 x_275 x_276) (DeqL_0 x_277))))
(assert (forall ((x_278 Nat_0) (x_279 E_0) (x_280 E_0))
	(diseqE_0 (EnqL_0 x_278 x_279) (DeqR_0 x_280))))
(assert (forall ((x_281 Nat_0) (x_282 E_0) (x_283 E_0) (x_284 E_0))
	(diseqE_0 (EnqL_0 x_281 x_282) (App_0 x_283 x_284))))
(assert (forall ((x_285 E_0) (x_286 Nat_0) (x_287 Nat_0) (x_288 E_0))
	(diseqE_0 (EnqR_0 x_285 x_286) (EnqL_0 x_287 x_288))))
(assert (forall ((x_289 E_0) (x_290 Nat_0) (x_291 E_0))
	(diseqE_0 (DeqL_0 x_289) (EnqL_0 x_290 x_291))))
(assert (forall ((x_292 E_0) (x_293 Nat_0) (x_294 E_0))
	(diseqE_0 (DeqR_0 x_292) (EnqL_0 x_293 x_294))))
(assert (forall ((x_295 E_0) (x_296 E_0) (x_297 Nat_0) (x_298 E_0))
	(diseqE_0 (App_0 x_295 x_296) (EnqL_0 x_297 x_298))))
(assert (forall ((x_299 E_0) (x_300 Nat_0) (x_301 E_0))
	(diseqE_0 (EnqR_0 x_299 x_300) (DeqL_0 x_301))))
(assert (forall ((x_302 E_0) (x_303 Nat_0) (x_304 E_0))
	(diseqE_0 (EnqR_0 x_302 x_303) (DeqR_0 x_304))))
(assert (forall ((x_305 E_0) (x_306 Nat_0) (x_307 E_0) (x_308 E_0))
	(diseqE_0 (EnqR_0 x_305 x_306) (App_0 x_307 x_308))))
(assert (forall ((x_309 E_0) (x_310 E_0) (x_311 Nat_0))
	(diseqE_0 (DeqL_0 x_309) (EnqR_0 x_310 x_311))))
(assert (forall ((x_312 E_0) (x_313 E_0) (x_314 Nat_0))
	(diseqE_0 (DeqR_0 x_312) (EnqR_0 x_313 x_314))))
(assert (forall ((x_315 E_0) (x_316 E_0) (x_317 E_0) (x_318 Nat_0))
	(diseqE_0 (App_0 x_315 x_316) (EnqR_0 x_317 x_318))))
(assert (forall ((x_319 E_0) (x_320 E_0))
	(diseqE_0 (DeqL_0 x_319) (DeqR_0 x_320))))
(assert (forall ((x_321 E_0) (x_322 E_0) (x_323 E_0))
	(diseqE_0 (DeqL_0 x_321) (App_0 x_322 x_323))))
(assert (forall ((x_324 E_0) (x_325 E_0))
	(diseqE_0 (DeqR_0 x_324) (DeqL_0 x_325))))
(assert (forall ((x_326 E_0) (x_327 E_0) (x_328 E_0))
	(diseqE_0 (App_0 x_326 x_327) (DeqL_0 x_328))))
(assert (forall ((x_329 E_0) (x_330 E_0) (x_331 E_0))
	(diseqE_0 (DeqR_0 x_329) (App_0 x_330 x_331))))
(assert (forall ((x_332 E_0) (x_333 E_0) (x_334 E_0))
	(diseqE_0 (App_0 x_332 x_333) (DeqR_0 x_334))))
(assert (forall ((x_335 Nat_0) (x_336 E_0) (x_337 Nat_0) (x_338 E_0))
	(=> (diseqNat_0 x_335 x_337)
	    (diseqE_0 (EnqL_0 x_335 x_336) (EnqL_0 x_337 x_338)))))
(assert (forall ((x_335 Nat_0) (x_336 E_0) (x_337 Nat_0) (x_338 E_0))
	(=> (diseqE_0 x_336 x_338)
	    (diseqE_0 (EnqL_0 x_335 x_336) (EnqL_0 x_337 x_338)))))
(assert (forall ((x_339 E_0) (x_340 Nat_0) (x_341 E_0) (x_342 Nat_0))
	(=> (diseqE_0 x_339 x_341)
	    (diseqE_0 (EnqR_0 x_339 x_340) (EnqR_0 x_341 x_342)))))
(assert (forall ((x_339 E_0) (x_340 Nat_0) (x_341 E_0) (x_342 Nat_0))
	(=> (diseqNat_0 x_340 x_342)
	    (diseqE_0 (EnqR_0 x_339 x_340) (EnqR_0 x_341 x_342)))))
(assert (forall ((x_343 E_0) (x_344 E_0))
	(=> (diseqE_0 x_343 x_344)
	    (diseqE_0 (DeqL_0 x_343) (DeqL_0 x_344)))))
(assert (forall ((x_345 E_0) (x_346 E_0))
	(=> (diseqE_0 x_345 x_346)
	    (diseqE_0 (DeqR_0 x_345) (DeqR_0 x_346)))))
(assert (forall ((x_347 E_0) (x_348 E_0) (x_349 E_0) (x_350 E_0))
	(=> (diseqE_0 x_347 x_349)
	    (diseqE_0 (App_0 x_347 x_348) (App_0 x_349 x_350)))))
(assert (forall ((x_347 E_0) (x_348 E_0) (x_349 E_0) (x_350 E_0))
	(=> (diseqE_0 x_348 x_350)
	    (diseqE_0 (App_0 x_347 x_348) (App_0 x_349 x_350)))))
(declare-fun take_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_13)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_164 Nat_0) (x_46 list_0) (z_0 Nat_0) (xs_0 list_0) (x_0 Nat_0))
	(=>	(and (gt_0 x_0 Z_13)
			(take_0 x_46 x_164 xs_0)
			(minus_0 x_164 x_0 (Z_14 Z_13)))
		(take_0 (cons_0 z_0 x_46) x_0 (cons_0 z_0 xs_0)))))
(assert (forall ((x_0 Nat_0) (y_0 list_0))
	(=> (le_0 x_0 Z_13)
	    (take_0 nil_0 x_0 y_0))))
(assert (forall ((x_0 Nat_0))
	(=> (gt_0 x_0 Z_13)
	    (take_0 nil_0 x_0 nil_0))))
(declare-fun tail_1 (list_0 list_0) Bool)
(assert (forall ((x_49 list_0) (y_1 Nat_0))
	(tail_1 x_49 (cons_0 y_1 x_49))))
(assert (tail_1 nil_0 nil_0))
(declare-fun length_0 (Nat_0 list_0) Bool)
(assert (forall ((x_165 Nat_0) (x_52 Nat_0) (y_2 Nat_0) (l_0 list_0))
	(=>	(and (length_0 x_52 l_0)
			(add_0 x_165 (Z_14 Z_13) x_52))
		(length_0 x_165 (cons_0 y_2 l_0)))))
(assert (length_0 Z_13 nil_0))
(declare-fun init_0 (list_0 list_0) Bool)
(assert (forall ((x_55 list_0) (x_4 Nat_0) (x_5 list_0) (y_3 Nat_0))
	(=> (init_0 x_55 (cons_0 x_4 x_5))
	    (init_0 (cons_0 y_3 x_55) (cons_0 y_3 (cons_0 x_4 x_5))))))
(assert (forall ((y_3 Nat_0))
	(init_0 nil_0 (cons_0 y_3 nil_0))))
(assert (init_0 nil_0 nil_0))
(declare-fun fstL_0 (Maybe_0 Q_0) Bool)
(assert (forall ((x_10 Nat_0) (x_11 list_0) (z_2 list_0))
	(fstL_0 (Just_0 x_10) (Q_1 (cons_0 x_10 x_11) z_2))))
(assert (forall ((x_8 Nat_0) (x_9 list_0) (y_5 Nat_0))
	(fstL_0 Nothing_0 (Q_1 nil_0 (cons_0 y_5 (cons_0 x_8 x_9))))))
(assert (forall ((y_5 Nat_0))
	(fstL_0 (Just_0 y_5) (Q_1 nil_0 (cons_0 y_5 nil_0)))))
(assert (fstL_0 Nothing_0 (Q_1 nil_0 nil_0)))
(declare-fun fromMaybe_0 (Nat_0 Nat_0 Maybe_0) Bool)
(assert (forall ((x_62 Nat_0) (x_12 Nat_0))
	(fromMaybe_0 x_62 x_12 (Just_0 x_62))))
(assert (forall ((x_12 Nat_0))
	(fromMaybe_0 x_12 x_12 Nothing_0)))
(declare-fun fromMaybe_1 (Q_0 Q_0 Maybe_1) Bool)
(assert (forall ((x_64 Q_0) (x_13 Q_0))
	(fromMaybe_1 x_64 x_13 (Just_1 x_64))))
(assert (forall ((x_13 Q_0))
	(fromMaybe_1 x_13 x_13 Nothing_1)))
(declare-fun empty_1 (Q_0) Bool)
(assert (empty_1 (Q_1 nil_0 nil_0)))
(declare-fun drop_0 (list_0 Nat_0 list_0) Bool)
(assert (forall ((x_67 list_0) (x_14 Nat_0))
	(=> (le_0 x_14 Z_13)
	    (drop_0 x_67 x_14 x_67))))
(assert (forall ((x_166 Nat_0) (x_68 list_0) (z_5 Nat_0) (xs_2 list_0) (x_14 Nat_0))
	(=>	(and (gt_0 x_14 Z_13)
			(drop_0 x_68 x_166 xs_2)
			(minus_0 x_166 x_14 (Z_14 Z_13)))
		(drop_0 x_68 x_14 (cons_0 z_5 xs_2)))))
(assert (forall ((x_70 list_0) (x_14 Nat_0))
	(=> (le_0 x_14 Z_13)
	    (drop_0 x_70 x_14 x_70))))
(assert (forall ((x_14 Nat_0))
	(=> (gt_0 x_14 Z_13)
	    (drop_0 nil_0 x_14 nil_0))))
(declare-fun halve_0 (pair_2 list_0) Bool)
(assert (forall ((x_74 list_0) (x_75 list_0) (x_72 Nat_0) (k_0 Nat_0) (x_15 list_0))
	(=>	(and (take_0 x_74 k_0 x_15)
			(drop_0 x_75 k_0 x_15)
			(length_0 x_72 x_15)
			(div_0 k_0 x_72 (Z_14 (Z_14 Z_13))))
		(halve_0 (pair_3 x_74 x_75) x_15))))
(declare-fun x_16 (list_0 list_0 list_0) Bool)
(assert (forall ((x_77 list_0) (z_6 Nat_0) (xs_3 list_0) (y_9 list_0))
	(=> (x_16 x_77 xs_3 y_9)
	    (x_16 (cons_0 z_6 x_77) (cons_0 z_6 xs_3) y_9))))
(assert (forall ((x_78 list_0))
	(x_16 x_78 nil_0 x_78)))
(declare-fun list_1 (list_0 E_0) Bool)
(assert (forall ((x_79 list_0) (x_80 list_0) (x_81 list_0) (a_0 E_0) (b_0 E_0))
	(=>	(and (list_1 x_80 a_0)
			(list_1 x_81 b_0)
			(x_16 x_79 x_80 x_81))
		(list_1 x_79 (App_0 a_0 b_0)))))
(assert (forall ((x_83 list_0) (x_84 list_0) (e_4 E_0))
	(=>	(and (list_1 x_84 e_4)
			(init_0 x_83 x_84))
		(list_1 x_83 (DeqR_0 e_4)))))
(assert (forall ((x_86 list_0) (x_87 list_0) (e_3 E_0))
	(=>	(and (list_1 x_87 e_3)
			(tail_1 x_86 x_87))
		(list_1 x_86 (DeqL_0 e_3)))))
(assert (forall ((x_89 list_0) (x_90 list_0) (e_2 E_0) (z_7 Nat_0))
	(=>	(and (list_1 x_90 e_2)
			(x_16 x_89 x_90 (cons_0 z_7 nil_0)))
		(list_1 x_89 (EnqR_0 e_2 z_7)))))
(assert (forall ((x_93 list_0) (y_10 Nat_0) (e_1 E_0))
	(=> (list_1 x_93 e_1)
	    (list_1 (cons_0 y_10 x_93) (EnqL_0 y_10 e_1)))))
(assert (list_1 nil_0 Empty_0))
(declare-fun reverse_0 (list_0 list_0) Bool)
(assert (forall ((x_95 list_0) (x_96 list_0) (y_11 Nat_0) (xs_4 list_0))
	(=>	(and (reverse_0 x_96 xs_4)
			(x_16 x_95 x_96 (cons_0 y_11 nil_0)))
		(reverse_0 x_95 (cons_0 y_11 xs_4)))))
(assert (reverse_0 nil_0 nil_0))
(declare-fun x_20 (Q_0 Q_0 Q_0) Bool)
(assert (forall ((x_100 list_0) (x_101 list_0) (x_102 list_0) (x_103 list_0) (vs_0 list_0) (ws_0 list_0) (xs_5 list_0) (ys_0 list_0))
	(=>	(and (reverse_0 x_100 ys_0)
			(x_16 x_101 xs_5 x_100)
			(reverse_0 x_102 vs_0)
			(x_16 x_103 ws_0 x_102))
		(x_20 (Q_1 x_101 x_103) (Q_1 xs_5 ys_0) (Q_1 vs_0 ws_0)))))
(declare-fun enqL_1 (Q_0 Nat_0 Q_0) Bool)
(assert (forall ((z_8 Nat_0) (x_23 list_0) (xs_6 list_0) (x_22 Nat_0))
	(enqL_1 (Q_1 (cons_0 x_22 xs_6) (cons_0 z_8 x_23)) x_22 (Q_1 xs_6 (cons_0 z_8 x_23)))))
(assert (forall ((x_107 list_0) (as_0 list_0) (bs_0 list_0) (xs_6 list_0) (x_22 Nat_0))
	(=>	(and (reverse_0 x_107 bs_0)
			(halve_0 (pair_3 as_0 bs_0) (cons_0 x_22 xs_6)))
		(enqL_1 (Q_1 as_0 x_107) x_22 (Q_1 xs_6 nil_0)))))
(declare-fun mkQ_0 (Q_0 list_0 list_0) Bool)
(assert (forall ((x_26 Nat_0) (x_27 list_0) (z_9 Nat_0) (x_25 list_0))
	(mkQ_0 (Q_1 (cons_0 z_9 x_25) (cons_0 x_26 x_27)) (cons_0 z_9 x_25) (cons_0 x_26 x_27))))
(assert (forall ((x_111 list_0) (as_2 list_0) (bs_2 list_0) (z_9 Nat_0) (x_25 list_0))
	(=>	(and (reverse_0 x_111 bs_2)
			(halve_0 (pair_3 as_2 bs_2) (cons_0 z_9 x_25)))
		(mkQ_0 (Q_1 as_2 x_111) (cons_0 z_9 x_25) nil_0))))
(assert (forall ((x_114 list_0) (as_1 list_0) (bs_1 list_0) (y_14 list_0))
	(=>	(and (reverse_0 x_114 bs_1)
			(halve_0 (pair_3 as_1 bs_1) y_14))
		(mkQ_0 (Q_1 x_114 as_1) nil_0 y_14))))
(declare-fun deqL_1 (Maybe_1 Q_0) Bool)
(assert (forall ((x_116 Q_0) (x_33 Nat_0) (xs_7 list_0) (z_10 list_0))
	(=> (mkQ_0 x_116 xs_7 z_10)
	    (deqL_1 (Just_1 x_116) (Q_1 (cons_0 x_33 xs_7) z_10)))))
(assert (forall ((x_31 Nat_0) (x_32 list_0) (x_29 Nat_0))
	(deqL_1 Nothing_1 (Q_1 nil_0 (cons_0 x_29 (cons_0 x_31 x_32))))))
(assert (forall ((x_119 Q_0) (x_29 Nat_0))
	(=> (empty_1 x_119)
	    (deqL_1 (Just_1 x_119) (Q_1 nil_0 (cons_0 x_29 nil_0))))))
(assert (deqL_1 Nothing_1 (Q_1 nil_0 nil_0)))
(declare-fun deqR_1 (Maybe_1 Q_0) Bool)
(assert (forall ((x_121 Q_0) (x_39 Nat_0) (x_40 list_0) (x_35 Nat_0) (y_17 Nat_0) (ys_2 list_0))
	(=> (mkQ_0 x_121 (cons_0 x_35 (cons_0 x_39 x_40)) ys_2)
	    (deqR_1 (Just_1 x_121) (Q_1 (cons_0 x_35 (cons_0 x_39 x_40)) (cons_0 y_17 ys_2))))))
(assert (forall ((x_123 Q_0) (x_37 Nat_0) (x_38 list_0) (x_35 Nat_0))
	(=> (mkQ_0 x_123 (cons_0 x_35 nil_0) x_38)
	    (deqR_1 (Just_1 x_123) (Q_1 (cons_0 x_35 nil_0) (cons_0 x_37 x_38))))))
(assert (forall ((x_128 Q_0) (y_17 Nat_0) (ys_2 list_0))
	(=> (mkQ_0 x_128 nil_0 ys_2)
	    (deqR_1 (Just_1 x_128) (Q_1 nil_0 (cons_0 y_17 ys_2))))))
(assert (forall ((x_39 Nat_0) (x_40 list_0) (x_35 Nat_0))
	(deqR_1 Nothing_1 (Q_1 (cons_0 x_35 (cons_0 x_39 x_40)) nil_0))))
(assert (forall ((x_133 Q_0) (x_35 Nat_0))
	(=> (empty_1 x_133)
	    (deqR_1 (Just_1 x_133) (Q_1 (cons_0 x_35 nil_0) nil_0)))))
(assert (deqR_1 Nothing_1 (Q_1 nil_0 nil_0)))
(declare-fun enqR_1 (Q_0 Q_0 Nat_0) Bool)
(assert (forall ((x_135 Q_0) (xs_8 list_0) (ys_3 list_0) (y_18 Nat_0))
	(=> (mkQ_0 x_135 xs_8 (cons_0 y_18 ys_3))
	    (enqR_1 x_135 (Q_1 xs_8 ys_3) y_18))))
(declare-fun queue_0 (Q_0 E_0) Bool)
(assert (forall ((x_137 Q_0) (x_138 Q_0) (x_139 Q_0) (a_1 E_0) (b_1 E_0))
	(=>	(and (queue_0 x_138 a_1)
			(queue_0 x_139 b_1)
			(x_20 x_137 x_138 x_139))
		(queue_0 x_137 (App_0 a_1 b_1)))))
(assert (forall ((x_142 Q_0) (x_143 Maybe_1) (r_0 Q_0) (e_8 E_0))
	(=>	(and (deqR_1 x_143 r_0)
			(fromMaybe_1 x_142 r_0 x_143)
			(queue_0 r_0 e_8))
		(queue_0 x_142 (DeqR_0 e_8)))))
(assert (forall ((x_146 Q_0) (x_147 Maybe_1) (q_2 Q_0) (e_7 E_0))
	(=>	(and (deqL_1 x_147 q_2)
			(fromMaybe_1 x_146 q_2 x_147)
			(queue_0 q_2 e_7))
		(queue_0 x_146 (DeqL_0 e_7)))))
(assert (forall ((x_149 Q_0) (x_150 Q_0) (e_6 E_0) (z_12 Nat_0))
	(=>	(and (queue_0 x_150 e_6)
			(enqR_1 x_149 x_150 z_12))
		(queue_0 x_149 (EnqR_0 e_6 z_12)))))
(assert (forall ((x_152 Q_0) (x_153 Q_0) (y_19 Nat_0) (e_5 E_0))
	(=>	(and (queue_0 x_153 e_5)
			(enqL_1 x_152 y_19 x_153))
		(queue_0 x_152 (EnqL_0 y_19 e_5)))))
(assert (forall ((x_155 Q_0))
	(=> (empty_1 x_155)
	    (queue_0 x_155 Empty_0))))
(assert (forall ((x_157 Q_0) (x_158 Maybe_0) (x_43 Nat_0) (y_20 list_0) (e_9 E_0))
	(=>	(and (diseqMaybe_0 x_158 (Just_0 x_43))
			(list_1 (cons_0 x_43 y_20) e_9)
			(queue_0 x_157 e_9)
			(fstL_0 x_158 x_157))
		false)))
(assert (forall ((x_160 Q_0) (x_161 Maybe_0) (e_9 E_0))
	(=>	(and (diseqMaybe_0 x_161 Nothing_0)
			(list_1 nil_0 e_9)
			(queue_0 x_160 e_9)
			(fstL_0 x_161 x_160))
		false)))
(check-sat)
