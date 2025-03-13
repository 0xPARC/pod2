use actix_cors::Cors;
use actix_files::Files;
use actix_web::{App, HttpServer, middleware::Logger};
use actix_web::web;
use log::info;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use pod2::web::{
    PodStorage,
    get_pods, get_pod_by_id, create_signed_pod, import_pod, export_pod
};

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    env_logger::init_from_env(env_logger::Env::new().default_filter_or("info"));
    
    // Create pod storage
    let storage: web::Data<PodStorage> = web::Data::new(Arc::new(RwLock::new(HashMap::new())));
    
    info!("Starting POD2 web server at http://127.0.0.1:8080");
    
    HttpServer::new(move || {
        let cors = Cors::default()
            .allow_any_origin()
            .allow_any_method()
            .allow_any_header()
            .max_age(3600);
        
        App::new()
            .wrap(Logger::default())
            .wrap(cors)
            .app_data(storage.clone())
            // API routes
            .service(
                web::scope("/api")
                    .route("/pods", web::get().to(get_pods))
                    .route("/pods/{id}", web::get().to(get_pod_by_id))
                    .route("/pods", web::post().to(create_signed_pod))
                    .route("/pods/import", web::post().to(import_pod))
                    .route("/pods/{id}/export", web::get().to(export_pod))
            )
            // Serve static files from 'static' directory
            .service(Files::new("/", "static").index_file("index.html"))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}